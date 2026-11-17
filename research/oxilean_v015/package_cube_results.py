from pathlib import Path
import hashlib,json,subprocess,zipfile
W=Path(__file__).resolve().parent;O=W.parent/'outputs'
receipt=json.loads((O/'CUBE_PUSH_RECEIPT.json').read_text());assert receipt['status']=='verified'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={}
for name,base in [('MathCan','3f99a6e90a2fbb5f5889998c48b1fe7d9a10660a'),('Compactification-Theory','41829db0ae124516992e8ce9aa79707565e9b080')]:
 repo=W/name;row=next(r for r in receipt['repositories'] if r['repository']==name)
 def git(*a):return subprocess.check_output(['git','-C',str(repo),*a],stderr=subprocess.STDOUT).decode().strip()
 assert git('rev-parse','HEAD')==row['local_commit'] and not git('status','--porcelain')
 bundle=O/(name.replace('-','_')+'_cube.bundle')
 subprocess.run(['git','-C',str(repo),'bundle','create',str(bundle),row['branch'],'^'+base],check=True)
 subprocess.run(['git','-C',str(repo),'bundle','verify',str(bundle)],check=True,stdout=subprocess.DEVNULL)
 assert git('bundle','list-heads',str(bundle)).split()==[row['local_commit'],'refs/heads/'+row['branch']]
 files[bundle.name]=bundle
for name in ['CUBE_APPROXIMATION_REPORT.md','CUBE_ACCEPTANCE.json','CUBE_BUILD_RECEIPT.json','CUBE_VERIFICATION_SUMMARY.json',
 'CUBE_GIT_INDEX_VERIFICATION.json','CUBE_GIT_CONTENT_VERIFICATION.json','CUBE_PUSH_RECEIPT.json','FINAL_VALIDATION.json']:
 files[name]=O/name
files['ApproximationMathlib/CubeApproximation.lean']=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib/CubeApproximation.lean'
files['ApproximationMathlib.lean']=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib.lean'
archive=O/'oxilean_closed_cube_20261117.zip';assert not archive.exists()
expected={name:sha(p) for name,p in files.items()}
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for name,p in files.items():z.write(p,name)
with zipfile.ZipFile(archive) as z:
 assert set(z.namelist())==set(files)
 for name,digest in expected.items():assert hashlib.sha256(z.read(name)).hexdigest()==digest
result={'status':'verified','archive':archive.name,'sha256':sha(archive),'bytes':archive.stat().st_size,
 'files':expected,'repository_commits':{r['repository']:r['local_commit'] for r in receipt['repositories']},
 'scope':'Phase-only incremental bundles and verification receipts. Bundle prerequisites are the preceding ordered matrix commits; full replay evidence is in the MathCan bundle.'}
(O/'CUBE_PACKAGE_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in result.items() if k!='files'},indent=2))
