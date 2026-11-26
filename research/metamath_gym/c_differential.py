"""C Metamath differential check; treat crashes and inconclusive output as failures."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

def digest(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()

def check(exe, path, expect, timeout=30):
    path = path.resolve()
    if any(c in str(path) for c in ('"', '\n', '\r')):
        raise ValueError("unsupported database path")
    proc = subprocess.run(
        [str(exe.resolve()), f'read "{path}"', "verify proof *", "exit"],
        capture_output=True, text=True, timeout=timeout, check=False,
        stdin=subprocess.DEVNULL,
    )
    log = proc.stdout + proc.stderr
    verified = "All proofs in the database were verified" in log
    explicit = "?Error" in log
    if expect:
        if proc.returncode != 0 or not verified or explicit:
            raise RuntimeError(f"C verifier rejected {path}: {log[-2000:]}")
    elif proc.returncode not in (0, 1) or not explicit or verified:
        raise RuntimeError(f"C verifier did not explicitly reject {path}: {log[-2000:]}")
    return {"sha256": digest(path), "verified": expect}

def main():
    exe, root, upstream = map(Path, sys.argv[1:])
    local = json.loads((root / "receipt.json").read_text())
    negatives = sorted((root / "invalid").glob("*.mm"))
    if len(negatives) != local["masked_invalid_candidates"] + local["negative_dv_cases"]:
        raise RuntimeError("incomplete differential corpus")
    result = {
        "c_verifier_sha256": digest(exe),
        "valid": check(exe, root / "valid.mm", True),
        "dv_valid": check(exe, root / "dv-valid.mm", True),
        "set_mm_baseline": check(exe, upstream, True, timeout=300),
        "negative_rejections": {},
    }
    for path in negatives:
        result["negative_rejections"][path.name] = check(exe, path, False)["sha256"]
    (root / "c-receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"positive_fixture_proofs": local["masked_valid_candidates"] + 1, "negative_cases": len(negatives), "set_mm_baseline": result["set_mm_baseline"]}))

if __name__ == "__main__":
    main()
