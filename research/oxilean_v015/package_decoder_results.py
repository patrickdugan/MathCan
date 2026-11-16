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
(O/'README.md').write_text('''# Decoder and spatial-capture research handoff

Read DECODER_FORMALIZATION_REPORT.md for the 2026-11-16 continuation.
The 39 new theorem roots and prior 56 research roots are independently
replayed. The unchanged Hodge replay remains accepted. The full analytic
approximation theorem and dense compiler/resource proof remain open.

TETSUYA_FOLLOW_UP_DRAFT.md is prepared but unsent. The two research branches
were pushed as explicitly requested; PUSH_RECEIPT.json verifies their remote
heads. COMMITS.json records their exact commits and local bundle hashes.
The default branches were not modified by these pushes.

The archive contains all sources, raw NDJSON, verdicts, dependency graphs,
native/reference-parser comparisons, acceptance controls, and exact reference
trace fixtures. Runtime/toolchain binaries are not bundled. The old corpora
and control runs retain their own provenance and scopes. Generic Lean proofs
and exact circuit fixtures are not evidence of improved transformer training.
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
    if rel.endswith('.lean') and Path(rel).stem in {'Hodge','QuantizedJet','SpatialInterface','SpatialScalar',
         'SpatialRouting','SpatialNormalized','SpatialClipped','SentinelDecoder','DecodedJetCapture'}:
        members['MathCan/'+rel]=repo/rel
hashes={name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size_bytes':p.stat().st_size}
        for name,p in sorted(members.items())}
(O/'DELIVERABLE_HASHES.json').write_text(json.dumps(hashes,indent=2)+'\n',encoding='utf-8',newline='\n')
members['DELIVERABLE_HASHES.json']=O/'DELIVERABLE_HASHES.json'
archive=O/'oxilean_decoder_capture_20261116.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for name,p in sorted(members.items()): z.write(p,name)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for name,record in hashes.items(): assert hashlib.sha256(z.read(name)).hexdigest()==record['sha256']
print(json.dumps({'archive':str(archive),'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
    'bytes':archive.stat().st_size,'files':len(members),'commits':records},indent=2))
