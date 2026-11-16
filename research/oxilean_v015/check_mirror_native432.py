from pathlib import Path
import hashlib,json,os,subprocess,time
assert os.name=='posix'
W=Path(__file__).resolve().parent;R=W/'replay432/Synthesis'
m=json.loads((R/'mathlib_mirror.json').read_text())
assert m['status']=='matched'
assert m['artifact_receipt_sha256']==hashlib.sha256((W/'MATHLIB_ARTIFACT_RECEIPT.json').read_bytes()).hexdigest()
target=Path(m['target'])
assert target==Path('/dev/shm/oxilean-synthesis432-20261116/mathlib432-local')
manifest=target.parent/'runtime_checksums.sha256'
for rel in m['files']:
    assert not Path(rel).is_absolute() and '..' not in Path(rel).parts and '\n' not in rel
manifest.write_text(''.join(digest+'  '+str(target/rel)+'\n' for rel,digest in sorted(m['files'].items())))
started=time.monotonic()
result=subprocess.run(['sha256sum','--check','--status',str(manifest)])
assert result.returncode==0, result.returncode
checked=dict(m,checker='system sha256sum --check --status',elapsed_seconds=time.monotonic()-started,copied_bytes=0)
(R/'mathlib_mirror_after_native.json').write_text(json.dumps(checked,indent=2)+'\n')
print(json.dumps({key:value for key,value in checked.items() if key!='files'},indent=2),flush=True)
