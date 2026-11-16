from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

W=Path(__file__).resolve().parent
O=W.parent/'outputs'
def git(repo,*args):
    return subprocess.check_output(['git','-C',str(repo),*args],encoding='utf-8').strip()
records=[]
for name,base,bundle in [('MathCan','13151576dd83939f7850f7f3025a49fa98e370b8','MathCan_research.bundle'),
                         ('Compactification-Theory','714c5ba87bb17a16f1ce4814c02abde2d1093e9d','Compactification_Theory_research.bundle')]:
    repo=W/name
    assert not git(repo,'status','--porcelain')
    branch=git(repo,'branch','--show-current')
    head=git(repo,'rev-parse','HEAD')
    subprocess.run(['git','-C',str(repo),'bundle','create',str(O/bundle),base+'..'+branch],check=True,capture_output=True)
    subprocess.run(['git','-C',str(repo),'bundle','verify',str(O/bundle)],check=True,capture_output=True)
    records.append({'repository':name,'branch':branch,'commit':head,'base':base,'worktree_clean':True,
        'bundle':bundle,'bundle_sha256':hashlib.sha256((O/bundle).read_bytes()).hexdigest()})
push=json.loads((O/'PUSH_RECEIPT.json').read_text(encoding='utf-8'))
assert push['status']=='verified'
for record in records:
    p=next(p for p in push['repositories'] if p['repository']==record['repository'])
    assert p['local_commit']==p['remote_commit']==record['commit'] and p['verified']
(O/'COMMITS.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8',newline='\n')
(O/'README.md').write_text('''# Hamming/Taylor transport research handoff

Read HAMMING_TAYLOR_FORMALIZATION_REPORT.md for the latest 2026-11-16 work.
The 63 new theorem roots prove Hamming amplitude selection, finite polynomial
Taylor transport, fixed-width frame parsing and scheduled decoded spatial
capture. All 158 research theorem roots have independent replay evidence in
their four corpora. Hodge remains a separate unchanged accepted theorem.
The full smooth-function approximation and dense compiler/resource proofs
remain open; the report lists exact limits and remaining obligations.

The two research branches were pushed as requested. PUSH_RECEIPT.json verifies
their heads; COMMITS.json records local commits and verified bundle hashes.
No default branch was modified. The previous follow-up to Tetsuya was sent
after separate user approval; no additional message was sent in this phase.
The older draft files and reports retain their historical labels and scopes.

The archive contains proof sources, raw NDJSON, every declaration verdict,
dependency and axiom audits, source/proof-term comparisons, native kernel
logs, acceptance tamper controls, and exact implementation controls.
Runtime binaries and compiled oleans are not bundled. The prior finite
controls and reference fixtures remain separate from mathematical proofs
and from any claims about trained transformer performance.
''',encoding='utf-8',newline='\n')
members={}
for p in O.iterdir():
    if p.is_file() and p.suffix in {'.md','.json','.lean','.bundle','.gz'} and p.name!='DELIVERABLE_HASHES.json':
        members[p.name]=p
for name,prefix in [('MathCan','research/oxilean_v015'),('Compactification-Theory','research/quantization')]:
    repo=W/name
    for rel in git(repo,'ls-files',prefix).splitlines(): members[name+'/'+rel]=repo/rel
repo=W/'MathCan'
for rel in git(repo,'ls-files','MathCan').splitlines():
    if rel.endswith('.lean'):members['MathCan/'+rel]=repo/rel
hashes={name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size_bytes':p.stat().st_size}
        for name,p in sorted(members.items())}
(O/'DELIVERABLE_HASHES.json').write_text(json.dumps(hashes,indent=2)+'\n',encoding='utf-8',newline='\n')
members['DELIVERABLE_HASHES.json']=O/'DELIVERABLE_HASHES.json'
archive=O/'oxilean_hamming_taylor_capture_20261116.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for name,p in sorted(members.items()):z.write(p,name)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for name,record in hashes.items():assert hashlib.sha256(z.read(name)).hexdigest()==record['sha256']
print(json.dumps({'archive':str(archive),'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
    'bytes':archive.stat().st_size,'files':len(members),'commits':records},indent=2))
