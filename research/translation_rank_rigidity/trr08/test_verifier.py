#!/usr/bin/env python3
"""Focused Python controls for the TRR-08 verifier; never invokes Lean."""
from __future__ import annotations

import argparse
from contextlib import redirect_stdout
from datetime import datetime, timezone
import importlib.util
from io import StringIO
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("trr08_verifier", HERE / "verify_formalization.py")
assert SPEC is not None and SPEC.loader is not None
VERIFIER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFIER)


def source_guard_control(source_text: str, should_pass: bool) -> None:
    """Exercise main's actual source guard with every external command mocked."""
    with tempfile.TemporaryDirectory(prefix="trr08-verifier-control-") as directory:
        core = Path(directory)
        geometry = core / "geometry"
        geometry.mkdir()
        (geometry / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": "mathlib", "rev": VERIFIER.PINNED_MATHLIB},
        ]}))
        (core / "Control.lean").write_text(source_text)
        output = core / "receipt.json"
        proof_calls = []

        def fake_run(command, cwd, log, seconds):
            if command[-1] == "--version":
                text = "Lean (version 4.35.0, x86_64-unknown-linux-gnu)\n"
            elif command[-1] == "Control.lean":
                proof_calls.append(command)
                text = "'Control.checked' does not depend on any axioms\n"
            else:
                text = ""
            return subprocess.CompletedProcess(command, 0, text, "")

        argv = ["verify_formalization.py", "--core-root", str(core),
                "--geometry-root", str(geometry), "--output", str(output)]
        with patch.object(VERIFIER, "MODULES", [
            ("core", "Control.lean", ["Control.checked"]),
        ]), patch.object(VERIFIER, "run", side_effect=fake_run), \
                patch.object(VERIFIER.subprocess, "check_output",
                             return_value=VERIFIER.PINNED_MATHLIB), \
                patch.object(sys, "argv", argv), redirect_stdout(StringIO()):
            exit_code = VERIFIER.main()
        receipt = json.loads(output.read_text())
        if should_pass:
            assert exit_code == 0 and receipt["status"] == "passed"
            assert len(proof_calls) == 1
        else:
            assert exit_code == 1 and receipt["status"] == "failed"
            assert "Forbidden proof admission" in receipt["error"]
            assert not proof_calls


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core-root", type=Path, default=HERE.parents[2])
    parser.add_argument("--geometry-root", type=Path)
    parser.add_argument("--output", type=Path, default=HERE / "audit_verifier.json")
    args = parser.parse_args()
    core = args.core_root.resolve()
    roots = {"core": core, "geometry": (args.geometry_root or core / "experiments/trr08_geometry").resolve()}
    cases = []

    def record(name, action):
        action()
        cases.append({"name": name, "status": "passed"})

    def source_contract():
        all_names = []
        for group, relative, expected in VERIFIER.MODULES:
            source = (roots[group] / relative).read_text()
            names = re.findall(r"^#print axioms\s+([^\s]+)", source, re.M)
            prefix = "MathCan." + Path(relative).stem + "." if group == "core" else "TRR08Geometry."
            names = [name if "." in name else prefix + name for name in names]
            assert names == expected, (relative, names, expected)
            assert not re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", source), relative
            all_names.extend(expected)
        assert len(all_names) == len(set(all_names)) == 43
        assert len(VERIFIER.MODULES[0][2]) == 6
        assert sum(len(module[2]) for module in VERIFIER.MODULES[1:]) == 37

    record("exact_source_report_contract_6_plus_37", source_contract)
    expected = ["T.a", "T.b"]
    good = ("info: p.lean:1:0: 'T.a' depends on axioms: [propext,\n"
            " Classical.choice,\n Quot.sound]\n"
            "info: p.lean:2:0: 'T.b' does not depend on any axioms\n")

    def valid_reports():
        assert VERIFIER.parse_reports(good, expected) == {
            "T.a": ["propext", "Classical.choice", "Quot.sound"], "T.b": [],
        }

    record("parse_multiline_and_axiom_free_reports", valid_reports)
    rejected = {
        "missing_report": good.split("info: p.lean:2:0:")[0],
        "extra_report": good + "'T.c' does not depend on any axioms\n",
        "duplicate_report": good + "'T.a' does not depend on any axioms\n",
        "admitted_proof_axiom": good.replace("propext,", "sorryAx,"),
        "custom_axiom": good.replace("propext,", "My.unsound,"),
        "unchecked_reduction_axiom": good.replace("propext,", "Lean.ofReduceBool,"),
        "wrong_declaration_name": good.replace("'T.a'", "'T.aa'"),
        "malformed_axiom_separator": good.replace("propext,\n Classical.choice", "propext Classical.choice"),
        "unclosed_axiom_list": good.replace("Quot.sound]", "Quot.sound"),
        "empty_output": "",
    }
    for name, text in rejected.items():
        def reject(text=text):
            try:
                VERIFIER.parse_reports(text, expected)
            except ValueError:
                return
            raise AssertionError("Malformed or unauthorized report accepted")
        record("reject_" + name, reject)

    def tokens_rejected():
        for token in ("sorry", "admit", "axiom", "native_decide"):
            source_guard_control("theorem checked : True := by " + token + "\n", False)

    record("source_guard_rejects_all_four_tokens", tokens_rejected)
    record("source_guard_rejects_string_comment_masking", lambda: source_guard_control(
        'def s : String := "/-"\ntheorem hidden : True := by sorry\n-- -/\n', False))
    record("source_guard_conservatively_scans_comments", lambda: source_guard_control(
        "/- a forbidden sorry token inside a comment -/\n", False))
    record("source_guard_accepts_clean_source", lambda: source_guard_control(
        "theorem checked : True := by trivial\n", True))

    audit = {
        "schema": "trr08-verifier-controls-v1", "status": "passed",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Python parser, source contract and mocked source-guard controls only",
        "lean_invocations": 0,
        "verifier_sha256": VERIFIER.sha256(HERE / "verify_formalization.py"),
        "test_sha256": VERIFIER.sha256(Path(__file__)),
        "principal_report_count": 43, "new_principal_report_count": 37,
        "source_contract": [
            {"project": group, "path": relative, "report_count": len(expected),
             "source_sha256": VERIFIER.sha256(roots[group] / relative)}
            for group, relative, expected in VERIFIER.MODULES
        ],
        "cases": cases,
    }
    args.output.write_text(json.dumps(audit, indent=2) + "\n")
    print(json.dumps({"status": "passed", "cases": len(cases), "lean_invocations": 0,
                      "audit": str(args.output.resolve())}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
