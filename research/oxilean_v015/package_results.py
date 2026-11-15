from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

W=Path(__file__).resolve().parent
O=W.parent/"outputs"
def git(repo,*args):
    return subprocess.check_output(["git","-C",str(repo),*args]).decode().strip()
records=[]
for name,base,bundle in (("MathCan","13151576dd83939f7850f7f3025a49fa98e370b8","MathCan_research.bundle"),("Compactification-Theory","714c5ba87bb17a16f1ce4814c02abde2d1093e9d","Compactification_Theory_research.bundle")):
    r=W/name
    status=git(r,"status","--porcelain")
    assert status=="",(name,status)
    commit=git(r,"rev-parse","HEAD")
    branch=git(r,"branch","--show-current")
    cmd=["git","-C",str(r),"bundle","create",str(O/bundle),base+".."+branch]
    subprocess.run(cmd,check=True,capture_output=True)
    check=subprocess.run(["git","-C",str(r),"bundle","verify",str(O/bundle)],capture_output=True,text=True)
    assert check.returncode==0,check.stderr
    records.append({"repository":name,"branch":branch,"commit":commit,"base":base,"worktree_clean":True,"bundle":bundle,"bundle_sha256":hashlib.sha256((O/bundle).read_bytes()).hexdigest()})
(O/"COMMITS.json").write_text(json.dumps(records,indent=2)+"\n",encoding="utf-8",newline="\n")
readme="""# OxiLean and quantized-jet research handoff

Read OXILEAN_V015_REPLAY_REPORT.md first. The exact pinned Hodge replay is
accepted: 1,256 verified records with no unsupported or rejected records.
The fourteen earlier research lemmas and 42 additional ordered-field spatial
lemmas also replay independently. Read LEAN_FORMALIZATION_STATUS.md for the
proved safe-cell extraction theorem and remaining obligations. The full
analytic theorem is not Lean formalized.

COMMITS.json contains exact local branch names, commits, clean-worktree checks,
base prerequisites and bundle hashes. The two Git bundles contain the new
commits and require their listed base commits in an existing repository.
For example, from an existing MathCan clone containing its base commit:

```bash
git bundle verify /path/to/MathCan_research.bundle
git fetch /path/to/MathCan_research.bundle research/quantized-jet-replay-20261115:research/quantized-jet-replay-20261115
```

This is a local fetch command, not a push. Adapt the analogous branch/bundle
from COMMITS.json for Compactification-Theory.

The archive includes source, exact control inputs, all raw verdict JSON,
structural audits, native dependency graphs and validation logs under the
corresponding repository directories. MathCan/research/oxilean_v015/README.md
documents the scripts and existing runtime paths. No toolchain binaries are
installed or bundled. The already compiled checker remains in the original
workspace work/build directory, with its build/source fingerprints recorded.

The prior evaluation archive and its original scripts were unavailable.
The finite controls included here are newly written independent checks.
TETSUYA_PROPOSED_EXCHANGE.md is an unsent draft.
"""
(O/"README.md").write_text(readme,encoding="utf-8",newline="\n")
members={}
for p in O.iterdir():
    if p.is_file() and p.suffix in (".md",".json",".lean",".bundle",".gz") and p.name!="DELIVERABLE_HASHES.json":
        members[p.name]=p
for repo,prefix in ((W/"MathCan","research/oxilean_v015"),(W/"Compactification-Theory","research/quantization")):
    paths=git(repo,"ls-files",prefix).splitlines()
    for rel in paths:
        members[repo.name+"/"+rel]=repo/rel
for name,rel in (("MathCan","MathCan/QuantizedJet.lean"),("MathCan","MathCan/SpatialInterface.lean"),("MathCan","MathCan/Hodge.lean"),("MathCan","MathCan/SpatialScalar.lean"),("MathCan","MathCan/SpatialRouting.lean"),("MathCan","MathCan/SpatialNormalized.lean"),("MathCan","MathCan/SpatialClipped.lean"),("Compactification-Theory","note/bits-depth-lipschitz.html")):
    members[name+"/"+rel]=W/name/rel
hashes={name:{"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"size_bytes":p.stat().st_size} for name,p in sorted(members.items())}
(O/"DELIVERABLE_HASHES.json").write_text(json.dumps(hashes,indent=2)+"\n",encoding="utf-8",newline="\n")
members["DELIVERABLE_HASHES.json"]=O/"DELIVERABLE_HASHES.json"
archive=O/"oxilean_spatial_formalization_20261115.zip"
with zipfile.ZipFile(archive,"w",compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for name,p in sorted(members.items()): z.write(p,name)
with zipfile.ZipFile(archive) as z: assert z.testzip() is None
print(json.dumps({"commits":records,"archive":str(archive),"archive_bytes":archive.stat().st_size,"archive_sha256":hashlib.sha256(archive.read_bytes()).hexdigest(),"files":len(members)},indent=2))
