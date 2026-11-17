from pathlib import Path
import hashlib,json,shutil
W=Path(__file__).resolve().parent;R=W/'replay432/Sharp'
ram=Path(r'\\wsl.localhost\Ubuntu\dev\shm\oxilean-sharp432-20261117')
src=ram/'results'
v=json.loads((src/'verdicts.json').read_text());c=json.loads((src/'source_export_comparison.json').read_text())
assert v['totals']['unsupported']==v['totals']['rejected']==0 and c['status']=='matched'
assert (src/'direct_kernel.log').read_text().strip().endswith('Accepted ApproximationMathlib.SharpTransport')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records={}
for p in src.iterdir():
 if not p.is_file():continue
 dest=R/p.name
 before=sha(p);shutil.copyfile(p,dest);assert sha(dest)==before,p.name
 records[p.name]=before
lib=R/'lib/ApproximationMathlib';lib.mkdir(parents=True,exist_ok=True)
for p in (ram/'lib/ApproximationMathlib').glob('SharpTransport.*'):
 before=sha(p);dest=lib/p.name;shutil.copyfile(p,dest);assert sha(dest)==before
 records['lib/ApproximationMathlib/'+p.name]=before
assert 'lib/ApproximationMathlib/SharpTransport.olean' in records
(R/'PROMOTION_RECEIPT.json').write_text(json.dumps({'status':'matched','source_linux':'/dev/shm/oxilean-sharp432-20261117/results','files':records},indent=2)+'\n')
print('Promoted and hash checked',len(records),'completed replay files.')
