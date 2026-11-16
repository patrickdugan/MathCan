from pathlib import Path
import hashlib,json,subprocess,zipfile
W=Path(__file__).resolve().parent;O=W.parent/'outputs'
def git(repo,*args):return subprocess.check_output(['git','-C',str(repo),*args],encoding='utf-8').strip()
records=[]
for name,base,bundle in [('MathCan','13151576dd83939f7850f7f3025a49fa98e370b8','MathCan_research.bundle'),
 ('Compactification-Theory','714c5ba87bb17a16f1ce4814c02abde2d1093e9d','Compactification_Theory_research.bundle')]:
 repo=W/name;assert not git(repo,'status','--porcelain')
 branch=git(repo,'branch','--show-current');head=git(repo,'rev-parse','HEAD')
 subprocess.run(['git','-C',str(repo),'bundle','create',str(O/bundle),base+'..'+branch],check=True,capture_output=True)
 subprocess.run(['git','-C',str(repo),'bundle','verify',str(O/bundle)],check=True,capture_output=True)
 records.append({'repository':name,'branch':branch,'commit':head,'base':base,'worktree_clean':True,
  'bundle':bundle,'bundle_sha256':hashlib.sha256((O/bundle).read_bytes()).hexdigest()})
push=json.loads((O/'PUSH_RECEIPT.json').read_text(encoding='utf-8'));assert push['status']=='verified'
for row in records:
 p=next(x for x in push['repositories'] if x['repository']==row['repository']);assert p['local_commit']==p['remote_commit']==row['commit']
(O/'COMMITS.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8',newline='\n')
(O/'README.md').write_text('''# Common gates and analytic Taylor handoff

Read COMMON_TAYLOR_FORMALIZATION_REPORT.md for the latest scope, proof counts,
verification and remaining obligations. This phase adds 40 authored roots and
12 attributed upstream foundations, reaching 210 research roots plus the separate
unchanged Hodge theorem. Full multivariate jet synthesis and dense network
arithmetic/resource proofs remain open.

The two research branches were pushed as requested. PUSH_RECEIPT.json verifies
the remote heads. COMMITS.json records clean local heads and verified Git bundles.
The source dependency, tool binaries and exported proof terms have pinned hashes.
Large analytic exports use deterministic .ndjson.gz files; their raw hashes are in
the acceptance receipts. Runtime binaries and compiled oleans are not bundled.

Mathlib is a workspace-local pinned dependency of the isolated analysis project.
The existing main MathCan Lean 4.35 toolchain is preserved. Analytic verification
uses Lean 4.32.0-rc1 and Mathlib v4.32.0-rc1. The 12 Taylor foundation roots retain
upstream attribution, provenance and the Apache-2.0 license.

Earlier reports and validation checkpoints retain their historical scope. The
latest verification is FINAL_VALIDATION.json and the common/analytic corpus
receipts. Previous empirical transformer results are separate from these proofs.
''',encoding='utf-8',newline='\n')
members={}
for p in O.iterdir():
 if p.is_file() and p.suffix in {'.md','.json','.lean','.bundle','.gz','.toml'} and p.name not in {'DELIVERABLE_HASHES.json','COMMON_TAYLOR_PACKAGE_RECEIPT.json'}:members[p.name]=p
for name,prefixes in [('MathCan',['research/oxilean_v015','research/approximation_mathlib432','MathCan']),
 ('Compactification-Theory',['research/quantization'])]:
 repo=W/name
 for prefix in prefixes:
  for rel in git(repo,'ls-files',prefix).splitlines():
   p=repo/rel
   if p.is_file():members[name+'/'+rel]=p
hashes={name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size_bytes':p.stat().st_size} for name,p in sorted(members.items())}
(O/'DELIVERABLE_HASHES.json').write_text(json.dumps(hashes,indent=2)+'\n',encoding='utf-8',newline='\n')
members['DELIVERABLE_HASHES.json']=O/'DELIVERABLE_HASHES.json'
archive=O/'oxilean_common_taylor_20261116.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for name,p in sorted(members.items()):z.write(p,name)
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None
 for name,row in hashes.items():assert hashlib.sha256(z.read(name)).hexdigest()==row['sha256']
result={'archive':str(archive),'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'bytes':archive.stat().st_size,'files':len(members),'commits':records}
(O/'COMMON_TAYLOR_PACKAGE_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(result,indent=2))
