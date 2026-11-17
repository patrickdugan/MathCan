from pathlib import Path
import hashlib,json,shutil
W=Path(__file__).resolve().parent;R=W/'replay432/Matrix'
ram=Path(r'\\wsl.localhost\Ubuntu\dev\shm\oxilean-sharp432-20261117');src=ram/'matrix-results'
v=json.loads((src/'verdicts.json').read_text(encoding='utf-8'));c=json.loads((src/'source_export_comparison.json').read_text(encoding='utf-8'))
assert v['totals']['unsupported']==v['totals']['rejected']==0 and c['status']=='matched'
assert 'Accepted ApproximationMathlib.WordTransport' in (src/'direct_kernel.log').read_text(encoding='utf-8')
records={};sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for p in src.iterdir():
 if not p.is_file():continue
 digest=sha(p);dest=R/p.name;shutil.copyfile(p,dest);assert sha(dest)==digest
 records[p.name]=digest
lib=R/'lib/ApproximationMathlib';lib.mkdir(parents=True,exist_ok=True)
for p in (ram/'lib/ApproximationMathlib').glob('WordTransport.*'):
 digest=sha(p);dest=lib/p.name;shutil.copyfile(p,dest);assert sha(dest)==digest
 records['lib/ApproximationMathlib/'+p.name]=digest
(R/'PROMOTION_RECEIPT.json').write_text(json.dumps({'status':'matched','files':records},indent=2)+'\n',encoding='utf-8',newline='\n')
print('Promoted',len(records),'hash-checked replay artifacts.')
