from pathlib import Path
import hashlib,json,subprocess
W=Path(__file__).resolve().parent;R=W/'replay432/Cube'
ram=Path(r'\\wsl.localhost\Ubuntu\dev\shm\oxilean-sharp432-20261117')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=W/'MathCan/MathCan/SpatialInterface.lean';data=source.read_bytes()
prior=json.loads((W/'replay432/Lemmas/ACCEPTANCE.json').read_text())
assert prior['status']=='accepted'
expected=next(v for k,v in prior['source_sha256'].items() if k.endswith('SpatialInterface.lean'))
assert sha(source)==expected
root=ram/'cube-legacy-source';(root/'MathCan').mkdir(parents=True,exist_ok=True);(root/'lib/MathCan').mkdir(parents=True,exist_ok=True)
frozen=root/'MathCan/SpatialInterface.lean';frozen.write_bytes(data)
command='source /dev/shm/oxilean-sharp432-20261117/cube_env432.sh; cd /dev/shm/oxilean-sharp432-20261117/cube-legacy-source; lean -j2 -o lib/MathCan/SpatialInterface.olean MathCan/SpatialInterface.lean > original_spatial_native.log 2>&1'
subprocess.run(['wsl.exe','--cd','/tmp','-e','bash','--noprofile','--norc','-c',command],check=True)
old=W/'replay432/Lemmas/lib/MathCan/SpatialInterface.olean';fresh=root/'lib/MathCan/SpatialInterface.olean'
digest=sha(old);assert sha(fresh)==sha(ram/'lib/MathCan/SpatialInterface.olean')==digest
assert sha(frozen)==sha(source)==expected
log=(root/'original_spatial_native.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
receipt={'status':'byte_identical','source':'MathCan/SpatialInterface.lean','source_sha256':expected,
 'reference_olean':'replay432/Lemmas/lib/MathCan/SpatialInterface.olean','rebuilt_olean_sha256':digest,
 'reference_olean_sha256':digest,'lean':'4.32.0-rc1','method':'Frozen unchanged original source rebuilt with pinned Lean; entire olean byte-identical to the imported artifact.'}
for out in [R,ram/'cube-results']:
 (out/'SPATIAL_SOURCE_REBUILD.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
 (out/'SpatialInterface_source_native.log').write_text(log,encoding='utf-8',newline='\n')
print(json.dumps(receipt))
