#!/usr/bin/env python3
"""Replay the committed Lean extension and its declared axiom inventory."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-binary", type=Path,
                        help="explicit Lean executable; otherwise use lake env lean")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    receipt_path = Path(__file__).with_name("extension_validation.json")
    receipt = json.loads(receipt_path.read_text())
    for relative, expected in receipt["source_sha256"].items():
        actual = hashlib.sha256((root / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"Source hash differs: {relative}")
    command = [str(args.lean_binary)] if args.lean_binary else ["lake", "env", "lean"]
    logs = []
    for source in receipt["modules"]:
        result = subprocess.run(command + [source], cwd=root, text=True,
                                capture_output=True, check=False)
        if result.returncode != 0 or result.stderr:
            raise SystemExit(f"Lean check failed for {source}:\n{result.stdout}\n{result.stderr}")
        logs.append(result.stdout)
    log = "".join(logs)
    expected_log = Path(__file__).with_name("extension_axioms.log").read_text()
    if log != expected_log:
        raise SystemExit("Printed axiom reports differ from the committed log")
    reports = {}
    pattern = r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    for match in re.finditer(pattern, log):
        reports[match[1]] = [x.strip() for x in (match[2] or "").split(",") if x.strip()]
    if reports != receipt["axiom_dependencies"]:
        raise SystemExit("The declared theorem inventory differs from Lean's reports")
    forbidden = {"sorryAx", "Lean.ofReduceBool", "ofReduceBool"}
    if any(forbidden.intersection(axioms) for axioms in reports.values()):
        raise SystemExit("An admitted goal or native-evaluation axiom appeared")
    print(f"PASS: {len(receipt['modules'])} modules, {len(reports)} theorem reports, exact source hashes")


if __name__ == "__main__":
    main()
