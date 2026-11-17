from pathlib import Path
import hashlib,json
W=Path(__file__).resolve().parent;tc=W/'toolchains/lean-4.32.0-rc1-linux'
t=Path(r'\\wsl.localhost\Ubuntu\tmp\oxilean-sharp432-exec-20261117')
paths=[(p,p.relative_to(tc)) for p in (tc/'lib/lean').glob('*.so')]
paths += [(tc/'bin'/name,Path('bin')/name) for name in ['lean','leanchecker']]
paths += [(tc/'lib'/name,Path('lib')/alias) for name,alias in
 [('libc++.so.1.0','libc++.so.1'),('libc++abi.so.1.0','libc++abi.so.1'),('libunwind.so.1.0','libunwind.so.1'),('libatomic.so.1.2.0','libatomic.so.1')]]
receipt=[]
for source,rel in paths:
 data=source.read_bytes();target=t/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
 digest=hashlib.sha256(data).hexdigest();assert hashlib.sha256(target.read_bytes()).hexdigest()==digest
 receipt.append({'source':source.relative_to(tc).as_posix(),'target':rel.as_posix(),'sha256':digest})
(W/'replay432/Sharp/executable_mirror.json').write_text(json.dumps({'status':'matched','target_linux':'/tmp/oxilean-sharp432-exec-20261117','files':receipt},indent=2)+'\n',encoding='utf-8')
print('Copied and hash checked pinned executables and shared libraries',flush=True)
src=W/'replay432/lean4export-source/.lake/build/lib/lean'
dst=Path(r'\\wsl.localhost\Ubuntu\dev\shm\oxilean-sharp432-20261117\lib')
records={}
for source in src.rglob('*'):
 if not source.is_file() or not any(source.name.endswith(e) for e in ['.olean','.olean.server','.olean.private','.ir']):continue
 rel=source.relative_to(src);target=dst/rel;target.parent.mkdir(parents=True,exist_ok=True)
 data=source.read_bytes();digest=hashlib.sha256(data).hexdigest();target.write_bytes(data)
 assert hashlib.sha256(target.read_bytes()).hexdigest()==digest
 records[rel.as_posix()]=digest
(W/'replay432/Sharp/exporter_library_mirror.json').write_text(json.dumps({'status':'matched','files':records},indent=2)+'\n',encoding='utf-8',newline='\n')
print('Copied and hash checked exporter parser library',flush=True)
