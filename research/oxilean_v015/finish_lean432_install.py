"""Repair official archive symlinks using WSL filesystem semantics."""
from pathlib import Path
import json
import os

W=Path(os.environ.get("CAMPAIGN_WORK", Path(__file__).resolve().parent)).resolve()
root=(W/"toolchains/lean-4.32.0-rc1-linux").resolve()
links=[]
for line in (W/"lean432_archive_listing.txt").read_text().splitlines():
    if not line.startswith("l"):
        continue
    fields=line.split()
    marker=fields.index("->")
    name=fields[marker-1]
    target=fields[marker+1]
    assert name.startswith("lean-4.32.0-rc1-linux/")
    dest=W/"toolchains"/name
    resolved=(dest.parent/target).resolve()
    assert resolved.is_relative_to(root),(name,target)
    if not dest.exists() and not dest.is_symlink():
        os.symlink(target,dest)
    links.append({"path":str(dest.relative_to(W)),"target":target})
for link in links:
    dest=W/link["path"]
    assert dest.resolve().is_relative_to(root) and dest.exists(),(dest,link["target"])
(W/"lean432_symlinks.json").write_text(json.dumps(links,indent=2)+"\n")
print("Verified archive symlinks:",len(links))
