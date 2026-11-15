"""Run each pinned control separately and require explicit per-declaration data."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
from collections import Counter

root = Path(os.environ.get("CAMPAIGN_WORK", Path(__file__).resolve().parent)).resolve()
out = root / "control_results"
out.mkdir(exist_ok=True)
expected = {
    "ProjOutOfProp": (5, 0, 2), "ProjRecIndexed": (22, 0, 0),
    "RecRuleTruth": (12, 0, 3), "RecRuleJunk": (7, 0, 8),
    "RecRuleControl": (3, 0, 2), "RecNameMixedStyleTruth": (9, 0, 4),
    "RecNameMixedStyle": (8, 0, 5), "RecNameFlat": (7, 0, 8),
}
expected_rejections = {
    "ProjOutOfProp": {"ProjOutOfProp.wit", "ProjOutOfProp.false_of_proj"},
    "ProjRecIndexed": set(),
    "RecRuleTruth": {"bad_val_is_f", "bad_f_eq_t", "boom"},
    "RecRuleJunk": {"T", "val", "fst", "val_eq", "honest_val_is_t", "bad_val_is_f", "bad_f_eq_t", "boom"},
    "RecRuleControl": {"ctrl_thm_junk_is_proof", "ctrl_def_junk"},
    "RecNameMixedStyleTruth": {"A.rec", "get_X_is_f", "bad_f_eq_t", "boom"},
    "RecNameMixedStyle": {"A", "X", "get_X_is_f", "bad_f_eq_t", "boom"},
    "RecNameFlat": {"T", "val", "fst", "val_eq", "honest_val_is_t", "bad_val_is_f", "bad_f_eq_t", "boom"},
}
summaries = []
for name, counts in expected.items():
    source = root / "oxilean/tests/fixtures/lean4export" / (name + ".ndjson")
    report = out / (name + ".json")
    cmd = [str(root / "build/oxilean-verify"), "--no-color", "--json-full", "--json", str(report), str(source)]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    (out / (name + ".stdout.log")).write_text(proc.stdout)
    (out / (name + ".stderr.log")).write_text(proc.stderr)
    item = {"fixture": name, "command": cmd, "exit_code": proc.returncode,
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(), "expected_counts": counts}
    if not report.exists():
        item.update(status="infrastructure_failure", error="No JSON report generated")
    else:
        r = json.loads(report.read_text())
        measured = tuple(r["totals"][k] for k in ("verified", "unsupported", "rejected"))
        assert r["input"]["sha256"] == item["sha256"]
        assert "decls" in r and len(r["decls"]) == sum(counts), r
        actual = Counter(d["verdict"] for d in r["decls"])
        assert tuple(actual[k] for k in ("verified", "unsupported", "rejected")) == counts
        assert {d["name"] for d in r["decls"] if d["verdict"] == "rejected"} == expected_rejections[name]
        assert len({d["name"] for d in r["decls"]}) == len(r["decls"])
        assert measured == counts, (name, measured, counts)
        assert proc.returncode == (1 if counts[2] else 0)
        item.update(status="expected_verdicts_observed", counts=dict(zip(("verified", "unsupported", "rejected"), measured)), declarations=r["decls"])
    summaries.append(item)
    print(name, item["status"], item.get("counts"), flush=True)
(out / "summary.json").write_text(json.dumps(summaries, indent=2) + "\n")
assert all(x["status"] == "expected_verdicts_observed" for x in summaries)
