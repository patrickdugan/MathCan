from pathlib import Path
import hashlib,json,subprocess,zipfile
W=Path(__file__).resolve().parent;O=W.parent/'outputs'
receipt=json.loads((O/'SHARP_PUSH_RECEIPT.json').read_text());assert receipt['status']=='verified'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={}
for name,base in [('MathCan','1068f4f62f9b020353a2110e734f0dd680ff6754'),('Compactification-Theory','e64226250f1e3ac181a619f3f1a367dac20b7c3a')]:
 repo=W/name;row=next(r for r in receipt['repositories'] if r['repository']==name)
 def git(*a):return subprocess.check_output(['git','-C',str(repo),*a],stderr=subprocess.STDOUT).decode().strip()
 assert git('rev-parse','HEAD')==row['local_commit'] and not git('status','--porcelain')
 bundle=O/(name.replace('-','_')+'_sharp.bundle')
 subprocess.run(['git','-C',str(repo),'bundle','create',str(bundle),row['branch'],'^'+base],check=True)
 subprocess.run(['git','-C',str(repo),'bundle','verify',str(bundle)],check=True,stdout=subprocess.DEVNULL)
 assert git('bundle','list-heads',str(bundle)).split()==[row['local_commit'],'refs/heads/'+row['branch']]
 files[bundle.name]=bundle
for name in ['SHARP_TRANSPORT_REPORT.md','SHARP_ACCEPTANCE.json','SHARP_BUILD_RECEIPT.json','SHARP_VERIFICATION_SUMMARY.json',
 'SHARP_GIT_INDEX_VERIFICATION.json','SHARP_GIT_CONTENT_VERIFICATION.json','SHARP_PUSH_RECEIPT.json','FINAL_VALIDATION.json']:
 files[name]=O/name
files['ApproximationMathlib/SharpTransport.lean']=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib/SharpTransport.lean'
files['ApproximationMathlib.lean']=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib.lean'
archive=O/'oxilean_sharp_transport_20261117.zip';assert not archive.exists()
expected={name:sha(p) for name,p in files.items()}
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for name,p in files.items():z.write(p,name)
with zipfile.ZipFile(archive) as z:
 assert set(z.namelist())==set(files)
 for name,digest in expected.items():assert hashlib.sha256(z.read(name)).hexdigest()==digest
result={'status':'verified','archive':archive.name,'sha256':sha(archive),'bytes':archive.stat().st_size,
 'files':expected,'repository_commits':{r['repository']:r['local_commit'] for r in receipt['repositories']},
 'scope':'Phase-only incremental bundles and verification receipts. Bundle prerequisites are the preceding synthesis commits; full replay evidence is in the MathCan bundle.'}
(O/'SHARP_PACKAGE_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in result.items() if k!='files'},indent=2))
