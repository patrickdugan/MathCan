from pathlib import Path
import hashlib,json,subprocess
W=Path(__file__).resolve().parent;ML=W/'mathlib432-local'
PIN='360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56'
S=json.loads((W/'MATHLIB_SOURCE_RECEIPT.json').read_text(encoding='utf-8'))
P=json.loads((W/'MATHLIB_PACKAGE_RECEIPT.json').read_text(encoding='utf-8'))
A=json.loads((W/'MATHLIB_ARTIFACT_RECEIPT.json').read_text(encoding='utf-8'))
assert S['revision']==A['mathlib_revision']==PIN and A['status']=='complete'
assert subprocess.check_output(['git','-C',str(ML),'rev-parse','HEAD'],text=True).strip()==PIN
assert len(A['modules'])==len({r['module'] for r in A['modules']})==2145
for rel,expected in S['verified_git_blobs'].items():
 data=(ML/rel).read_bytes();actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert actual==expected,(rel,actual,expected)
manifest=json.loads((ML/'lake-manifest.json').read_text(encoding='utf-8'))
for package in manifest['packages']:
 name=package['name'];packageRoot=ML/'.lake/packages'/name
 assert P[name]['revision']==package['rev']
 assert subprocess.check_output(['git','-C',str(packageRoot),'rev-parse','HEAD'],text=True).strip()==package['rev']
 for rel,expected in P[name]['git_blobs'].items():
  data=(packageRoot/rel).read_bytes();actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert actual==expected,(name,rel)
count=0
for module in A['modules']:
 for rel,expected in module['retained_files'].items():
  relative=Path(rel)
  assert not relative.is_absolute() and '..' not in relative.parts
  path=ML/relative
  assert hashlib.sha256(path.read_bytes()).hexdigest()==expected,(module['module'],rel)
  count+=1
print(json.dumps({'status':'matched','mathlib_revision':PIN,'pinned_sources':len(S['verified_git_blobs']),
 'packages':len(P),'artifact_modules':len(A['modules']),'retained_artifact_files':count,
 'artifact_receipt_sha256':hashlib.sha256((W/'MATHLIB_ARTIFACT_RECEIPT.json').read_bytes()).hexdigest()}))
