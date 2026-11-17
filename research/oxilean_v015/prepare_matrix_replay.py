from pathlib import Path
import hashlib,json,re,shutil
W=Path(__file__).resolve().parent;R=W/'replay432/Matrix';R.mkdir(parents=True,exist_ok=True)
ram=Path(r'\\wsl.localhost\Ubuntu\dev\shm\oxilean-sharp432-20261117')
result=ram/'matrix-results';project=ram/'matrix-source';result.mkdir(parents=True,exist_ok=True)
module='WordTransport';source=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib'/f'{module}.lean'
data=source.read_bytes();sourcehash=hashlib.sha256(data).hexdigest()
frozen=project/'ApproximationMathlib'/source.name;frozen.parent.mkdir(parents=True,exist_ok=True);frozen.write_bytes(data)
assert hashlib.sha256(frozen.read_bytes()).hexdigest()==sourcehash
blocks=re.findall(r'^namespace (MathCan\.\w+)\n(.*?)^end \1\s*$',data.decode(),re.M|re.S);assert len(blocks)==2
roots=[ns+'.'+n for ns,body in blocks for n in re.findall(r'^(?:theorem|lemma) (\w+)',body,re.M)]
assert len(roots)==len(set(roots))==34
manifest={'modules':['ApproximationMathlib.WordTransport'],'sources':{'WordTransport':'research/approximation_mathlib432/ApproximationMathlib/WordTransport.lean'},
 'theorems':roots,'mathlib_revision':'360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56','vendor_roots':[]}
def write(name,text):
 (R/name).write_text(text,encoding='utf-8',newline='\n');(result/name).write_text(text,encoding='utf-8',newline='\n')
write('manifest.json',json.dumps(manifest,indent=2)+'\n');write('roots.txt','\n'.join(roots)+'\n');write('modules.txt','WordTransport\n')
s=(W/'replay432/CompareLemmas.lean').read_text(encoding='utf-8').replace('import MathCan.QuantizedJet\nimport MathCan.SpatialInterface','import ApproximationMathlib.WordTransport').replace('MathCan.SpatialInterface.capture_at_index','MathCan.WordCapture.decoded_approximation')
s+='\n'+'\n'.join('#print axioms '+name for name in roots)+'\n';write('CompareMatrix.lean',s)
write('DirectKernel.lean','''import LeanChecker
open Lean
unsafe def runMatrixKernelChecks : IO Unit := do
  initSearchPath (← findSysroot)
  IO.println "Checking ApproximationMathlib.WordTransport using pinned replayFromImports"
  replayFromImports `ApproximationMathlib.WordTransport
  IO.println "Accepted ApproximationMathlib.WordTransport"
#eval runMatrixKernelChecks
''')
write('source_before.sha256',sourcehash+'  /dev/shm/oxilean-sharp432-20261117/matrix-source/ApproximationMathlib/WordTransport.lean\n')
write('source_mirror.json',json.dumps({'status':'matched','source_sha256':{manifest['sources']['WordTransport']:sourcehash},
 'frozen_linux':'/dev/shm/oxilean-sharp432-20261117/matrix-source/ApproximationMathlib/WordTransport.lean'},indent=2)+'\n')
prior=W/'replay432/Sharp'
for name in ['runtime_mirror.json','executable_mirror.json','exporter_library_mirror.json','mathlib_mirror.json','mirror_used.json']:
 write(name,(prior/name).read_text(encoding='utf-8'))
receipt=json.loads((prior/'BUILD_RECEIPT.json').read_text(encoding='utf-8'));pins=receipt['binary_sha256']
before=[];cachepins=[];extra=[]
for rel,digest in pins.items():
 p=W/rel;assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
 before.append(digest+'  /mnt/c/Users/patri/Documents/Codex/2026-11-15/files-pasted-by-the-user-oxilean/work/'+rel+'\n')
 if p.name in ['lean4export','oxilean-verify']:
  dest=Path(r'\\wsl.localhost\Ubuntu\tmp\oxilean-sharp432-exec-20261117\bin')/p.name
  shutil.copyfile(p,dest);assert hashlib.sha256(dest.read_bytes()).hexdigest()==digest
  target='/tmp/oxilean-sharp432-exec-20261117/bin/'+p.name
  extra.append({'source':rel,'target_linux':target,'sha256':digest});cachepins.append(digest+'  '+target+'\n')
 elif p.name in ['lean','leanchecker']:
  cachepins.append(digest+'  /tmp/oxilean-sharp432-exec-20261117/bin/'+p.name+'\n')
 else:cachepins.append(digest+'  /dev/shm/oxilean-sharp432-20261117/toolchain-lib/LeanChecker.olean\n')
write('binary_before.sha256',''.join(before));write('cache_binary_before.sha256',''.join(cachepins))
write('extra_executable_mirror.json',json.dumps({'status':'matched','files':extra},indent=2)+'\n')
previous=[]
for p in (prior/'lib/ApproximationMathlib').glob('SharpTransport.*'):
 if not p.is_file():continue
 digest=hashlib.sha256(p.read_bytes()).hexdigest();dest=ram/'lib/ApproximationMathlib'/p.name
 assert hashlib.sha256(dest.read_bytes()).hexdigest()==digest
 previous.append({'source':'replay432/Sharp/lib/ApproximationMathlib/'+p.name,'target_linux':'/dev/shm/oxilean-sharp432-20261117/lib/ApproximationMathlib/'+p.name,'sha256':digest})
assert any(p['sha256']==receipt['olean_sha256']['ApproximationMathlib.SharpTransport'] for p in previous)
write('previous_module_mirror.json',json.dumps({'status':'matched','files':previous},indent=2)+'\n')
for name in ['matrix_env432.sh','run_matrix432.sh','check_matrix_mirrors.py','audit_export_fast.py']:
 shutil.copyfile(W/name,ram/name)
(ram/'matrix-dev/stop_lsp').write_text('stop')
print(json.dumps({'new_roots':len(roots),'source_sha256':sourcehash,'status':'frozen'}))
