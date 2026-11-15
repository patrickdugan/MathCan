"""Materialize exact pinned Git blobs in newly created, private worktrees."""
from pathlib import Path
import subprocess
import hashlib
import json

root = Path(__file__).resolve().parent
pins = {"MathCan": "13151576dd83939f7850f7f3025a49fa98e370b8", "oxilean": "3adb983d2aefc6a596bdc8b63438f54feecd1f55", "lean4export": "3de59f10bc4b4a0f2de698597aeb1246caa0df0a"}
manifest = {}
for name, pin in pins.items():
    repo = root / name
    assert subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"]).decode().strip() == pin
    entries = subprocess.check_output(["git", "-C", str(repo), "ls-tree", "-rz", pin]).split(b"\0")
    blobs = []
    for entry in entries:
        if not entry:
            continue
        meta, path = entry.split(b"\t", 1)
        mode, kind, oid = meta.split()
        if kind == b"blob" and mode != b"120000":
            blobs.append((path.decode(), oid.decode()))
    data = subprocess.check_output(["git", "-C", str(repo), "cat-file", "--batch"], input=("\n".join(oid for _, oid in blobs) + "\n").encode())
    offset = 0
    changed = 0
    sums = []
    for path, oid in blobs:
        end = data.index(b"\n", offset)
        header = data[offset:end].split()
        size = int(header[2])
        content = data[end + 1:end + 1 + size]
        offset = end + size + 2
        assert hashlib.sha1(b"blob " + str(size).encode() + b"\0" + content).hexdigest() == oid
        dest = repo / path
        if not dest.exists() or dest.read_bytes() != content:
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(content)
            changed += 1
        digest = hashlib.sha256(content).hexdigest()
        if name == "oxilean" and path.startswith(("crates/oxilean-kernel/", "crates/oxilean-export/", "crates/oxilean-verify/")):
            sums.append(f"{digest}  {name}/{path}")
    if sums:
        (root / "checker_source_sha256.txt").write_text("\n".join(sums) + "\n", encoding="utf-8", newline="\n")
    manifest[name] = {"commit": pin, "files": len(blobs), "line_endings_restored": changed}
(root / "source_materialization.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
