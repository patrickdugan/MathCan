"""Check every independent module and its exact exported axiom closure."""
import pathlib
import re
import subprocess
import sys

targets = {"CLN02": 8, "CLN03": 6, "CLN04": 3}
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = []
for module, expected in targets.items():
    p = pathlib.Path(module + ".lean")
    # Every theorem must be backed by Lean rather than an explicit postulate.
    src = p.read_text(encoding="utf-8")
    if re.search(r"(?m)^\s*(?:private\s+|protected\s+)?axiom\b|\b(?:sorry|admit)\b", src):
        bad.append(module + ": prohibited source token")
    run = subprocess.run(["lake", "env", "lean", str(p)],
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = run.stdout
    pathlib.Path(module + "-kernel.log").write_text(out, encoding="utf-8")
    print(out, flush=True)
    if run.returncode:
        bad.append(module + ": kernel exit " + str(run.returncode))
    declarations = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", out)
    if len(declarations) != expected:
        bad.append(module + ": expected " + str(expected) + " axiom reports, got " + str(len(declarations)))
    for name, raw in declarations:
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        if axioms - allowed:
            bad.append(name + ": unexpected axioms " + repr(axioms - allowed))
    if "sorryAx" in out or "declaration uses 'sorry'" in out:
        bad.append(module + ": incomplete proof")
print("CLN audit:", "FAIL" if bad else "PASS")
for err in bad:
    print(err, file=sys.stderr)
sys.exit(bool(bad))
