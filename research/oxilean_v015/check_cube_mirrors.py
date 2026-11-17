from pathlib import Path
import hashlib,json,sys,time
R=Path('/dev/shm/oxilean-sharp432-20261117/cube-results');phase=sys.argv[1]
assert phase in ['before','after'];checks=[];receipts={}
for name in ['runtime_mirror','executable_mirror','exporter_library_mirror','mathlib_mirror','extra_executable_mirror','previous_module_mirror']:
 m=json.loads((R/(name+'.json')).read_text(encoding='utf-8'));receipts[name]=m;assert m['status']=='matched'
 if name in ['extra_executable_mirror','previous_module_mirror']:
  checks += [(p['target_linux'],p['sha256']) for p in m['files']]
 elif name=='executable_mirror':checks += [(str(Path(m['target_linux'])/p['target']),p['sha256']) for p in m['files']]
 else:
  target=m.get('target_linux',m.get('target','/dev/shm/oxilean-sharp432-20261117/lib'))
  checks += [(str(Path(target)/rel),digest) for rel,digest in m['files'].items()]
start=time.monotonic()
for path,digest in checks:assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest,path
for name,value in receipts.items():
 (R/(name+'_'+phase+'.json')).write_text(json.dumps(dict(value,phase=phase,checker='Python hashlib.sha256 (OpenSSL)',elapsed_seconds=time.monotonic()-start),indent=2)+'\n')
print('All mirrored bytes matched:',len(checks),flush=True)
