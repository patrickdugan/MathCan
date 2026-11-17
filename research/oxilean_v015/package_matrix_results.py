from pathlib import Path
import hashlib,json,subprocess,zipfile
W=Path(__file__).resolve().parent;O=W.parent/'outputs'
receipt=json.loads((O/'MATRIX_PUSH_RECEIPT.json').read_text());assert receipt['status']=='verified'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={}
for name,base in [('MathCan','f30dbad0fd4f6a44ad67dd90e4f5637de83ee486'),('Compactification-Theory','5b119799c338bbd6db97a3e1240724b8897af627')]:
 repo=W/name;row=next(r for r in receipt['repositories'] if r['repository']==name)
 def git(*a):return subprocess.check_output(['git','-C',str(repo),*a],stderr=subprocess.STDOUT).decode().strip()
 assert git('rev-parse','HEAD')==row['local_commit'] and not git('status','--porcelain')
 bundle=O/(name.replace('-','_')+'_matrix.bundle')
 subprocess.run(['git','-C',str(repo),'bundle','create',str(bundle),row['branch'],'^'+base],check=True)
 subprocess.run(['git','-C',str(repo),'bundle','verify',str(bundle)],check=True,stdout=subprocess.DEVNULL)
 assert git('bundle','list-heads',str(bundle)).split()==[row['local_commit'],'refs/heads/'+row['branch']]
 files[bundle.name]=bundle
for name in ['MATRIX_TRANSPORT_REPORT.md','MATRIX_ACCEPTANCE.json','MATRIX_BUILD_RECEIPT.json','MATRIX_VERIFICATION_SUMMARY.json',
 'MATRIX_GIT_INDEX_VERIFICATION.json','MATRIX_GIT_CONTENT_VERIFICATION.json','MATRIX_PUSH_RECEIPT.json','FINAL_VALIDATION.json']:
 files[name]=O/name
files['ApproximationMathlib/WordTransport.lean']=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib/WordTransport.lean'
files['ApproximationMathlib.lean']=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib.lean'
archive=O/'oxilean_word_matrix_20261117.zip';assert not archive.exists()
expected={name:sha(p) for name,p in files.items()}
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for name,p in files.items():z.write(p,name)
with zipfile.ZipFile(archive) as z:
 assert set(z.namelist())==set(files)
 for name,digest in expected.items():assert hashlib.sha256(z.read(name)).hexdigest()==digest
result={'status':'verified','archive':archive.name,'sha256':sha(archive),'bytes':archive.stat().st_size,
 'files':expected,'repository_commits':{r['repository']:r['local_commit'] for r in receipt['repositories']},
 'scope':'Phase-only incremental bundles and verification receipts. Bundle prerequisites are the preceding sharp transport commits; full replay evidence is in the MathCan bundle.'}
(O/'MATRIX_PACKAGE_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in result.items() if k!='files'},indent=2))
