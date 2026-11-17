from pathlib import Path
import hashlib,json,subprocess,sys,time
W=Path(__file__).resolve().parent;R=W/'replay432/Sharp'
phase=sys.argv[1];assert phase in ['before','after']
runtime=json.loads((R/'runtime_mirror.json').read_text());exe=json.loads((R/'executable_mirror.json').read_text())
parser=json.loads((R/'exporter_library_mirror.json').read_text())
ml=json.loads((W/'replay432/Synthesis/mathlib_mirror.json').read_text())
checks=[]
for rel,digest in runtime['files'].items():checks.append((str(Path(runtime['target_linux'])/rel),digest))
for rec in exe['files']:checks.append((str(Path(exe['target_linux'])/rec['target']),rec['sha256']))
for rel,digest in ml['files'].items():checks.append((str(Path(ml['target'])/rel),digest))
for rel,digest in parser['files'].items():checks.append((str(Path(runtime['target_linux'])/'lib'/rel),digest))
manifest=Path(runtime['target_linux'])/'checksums_all.sha256'
manifest.write_text(''.join(digest+'  '+path+'\n' for path,digest in checks))
start=time.monotonic()
for path,digest in checks:
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest,path
for value,name in [(runtime,'runtime_mirror'),(exe,'executable_mirror'),(ml,'mathlib_mirror'),(parser,'exporter_library_mirror')]:
 value=dict(value,checker='Python hashlib.sha256 (OpenSSL SHA-256)',phase=phase,elapsed_seconds=time.monotonic()-start)
 (R/(name+'_'+phase+'.json')).write_text(json.dumps(value,indent=2)+'\n')
 if phase=='before' and name=='mathlib_mirror':
  (R/'mathlib_mirror.json').write_text(json.dumps(value,indent=2)+'\n')
  (R/'mirror_used.json').write_text((W/'replay432/Synthesis/mirror_used.json').read_text())
print('Verified all Lean runtime, executable and mathlib mirror bytes:',len(checks),flush=True)
