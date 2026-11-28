"""Differential check against an explicitly supplied upstream mmverify.py."""
import json
from pathlib import Path
import subprocess
import sys

def check(verifier, path, expect):
    proc = subprocess.run(
        [sys.executable, str(verifier), str(path), "-v", "1"],
        capture_output=True, text=True, timeout=30, check=False,
    )
    log = proc.stdout + proc.stderr
    if expect:
        if proc.returncode != 0 or "No errors were found." not in log:
            raise RuntimeError(f"unexpected rejection {path}: {log[-2000:]}")
    elif proc.returncode == 0 or "MMError:" not in log or "No errors were found." in log:
        raise RuntimeError(f"missing explicit rejection {path}: {log[-2000:]}")

def main():
    verifier, root = map(Path, sys.argv[1:])
    receipt = json.loads((root / "receipt.json").read_text())
    invalid = sorted((root / "invalid").glob("*.mm"))
    assert len(invalid) == receipt["masked_invalid_candidates"] + receipt["negative_dv_cases"]
    for name in ("valid.mm", "dv-valid.mm"):
        check(verifier, root / name, True)
    for path in invalid:
        check(verifier, path, False)
    print(json.dumps({"positive_databases": 2, "positive_proofs": receipt["masked_valid_candidates"] + 1, "explicit_negative_rejections": len(invalid)}))

if __name__ == "__main__":
    main()
