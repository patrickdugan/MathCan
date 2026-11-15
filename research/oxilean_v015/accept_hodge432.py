"""Fail-closed acceptance of the exact Hodge source/export/closure campaign."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import os
from audit_export import audit

W=Path(os.environ.get("CAMPAIGN_WORK", Path(__file__).resolve().parent)).resolve()
R=Path(os.environ.get("REPLAY_OUT", W/"replay432/Hodge"))
def read(name): return json.loads((R/name).read_text())
v=read("verdicts.json")
a=read("axiom-graph.json")
c=read("source_export_comparison.json")
sha=hashlib.sha256((R/"Hodge.ndjson").read_bytes()).hexdigest()
assert v["input"]["sha256"]==a["sha256"]==sha
assert v["tool"]["version"]=="0.1.5"
assert v["pins"]["lean4export_commit"]=="3de59f10bc4b4a0f2de698597aeb1246caa0df0a"
assert v["pins"]["file_lean_version"]=="4.32.0-rc1"
assert v["pins"]["file_lean_githash"]=="b4812ae53eea93439ad5dce5a5c26591c31cb697"
assert a["structurally_closed"] and a["unambiguous_names"] and not a["unsafe_records"]
assert a["closure_record_count"]<=a["record_count"]==len(v["decls"])
full=audit(R/"Hodge.ndjson")
(R/"full-export-graph.json").write_text(json.dumps(full,indent=2)+"\n")
assert full["structurally_closed"] and full["unambiguous_names"] and not full["unsafe_records"]
assert len({x["name"] for x in v["decls"]})==len(v["decls"])
byname={x["name"]:x for x in v["decls"]}
for node in full["records"]:
    primary=node["display_names"][0]
    assert byname[primary]["verdict"]=="verified",(primary,byname.get(primary))
assert byname["MathCan.Hodge.closed_path_gauge"]["verdict"]=="verified"
counts=Counter(x["verdict"] for x in v["decls"])
assert counts["unsupported"]==counts["rejected"]==0
assert v["totals"]["verified"]==counts["verified"]
axes=sorted(x["name"] for x in a["axioms"])
assert axes==["Quot.sound","propext"],axes
assert c["status"]=="matched"
assert c["constants_compared"]==sum(len(x["names"]) for x in full["records"])
assert all(x["type_equal"] and x["value_equal_after_metadata_normalization"] and x["level_parameters_equal"] for x in c["records"])
assert hashlib.sha256((W/"replay432/MathCan-source/MathCan/Hodge.lean").read_bytes()).hexdigest()=="6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5"
assert (R/"oxilean.exit-code").read_text().strip()=="0"
result={"status":"accepted", "target":"MathCan.Hodge.closed_path_gauge", "export_sha256":sha,
        "verdicts":{"verified":counts["verified"],"unsupported":0,"rejected":0},
        "dependency_closed":True,"source_statement_and_proof_match":True,
        "exported_constants_compared":c["constants_compared"],"axioms":axes,
        "target_dependency_records":a["closure_record_count"],
        "extra_export_records":[x["display_names"] for x in full["records"] if x["id"] not in {r["id"] for r in a["records"]}],
        "axiom_interpretation":"Conditional on Lean propext and quotient soundness, neither treated as a proved axiom",
        "native_lean":"4.32.0-rc1 accepted unchanged source", "leanchecker":"4.32.0-rc1 accepted",
        "normalization":"Only expression metadata and let nondep hints; no changed assumptions, reduction or substituted proof"}
(R/"ACCEPTANCE.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
