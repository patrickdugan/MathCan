from pathlib import Path
import hashlib,json,shutil,subprocess,time
W=Path(__file__).resolve().parent;ML=(W/'mathlib432-local').resolve()
linux='/mnt/'+W.drive[0].lower()+W.as_posix()[2:]
plan=json.loads((W/'mathlib-cache432/module-plan.json').read_text(encoding='utf-8'))
assert len(plan)==2145
previous=W/'MATHLIB_ARTIFACT_RECEIPT.json'
receipt=json.loads(previous.read_text(encoding='utf-8'))['modules'] if previous.exists() else []
done={r['module'] for r in receipt}
for row in receipt:
 for rel,digest in row['retained_files'].items():
  artifact=(ML/rel).resolve();assert artifact.is_relative_to(ML)
  assert hashlib.sha256(artifact.read_bytes()).hexdigest()==digest
plan=[row for row in plan if row['module'] not in done]
def windows(p):
 if p.startswith(linux+'/'):return (W/p[len(linux)+1:]).resolve()
 return (ML/p).resolve()
def checked(p):
 p=p.resolve()
 assert p.is_relative_to(ML),p
 return p
for start in range(0,len(plan),72):
 batch=plan[start:start+72]
 if shutil.disk_usage(W).free<120*1024**2:raise RuntimeError('Insufficient space before the next small extraction batch')
 files=[r['file'] for r in batch]
 for f in files:assert windows(f).is_relative_to(W/'mathlib-cache432'),f
 cmd=['wsl.exe','-d','Ubuntu','--cd',linux+'/mathlib432-local','--',linux+'/toolchains/lean-4.32.0-rc1-linux/bin/leantar','-f','-x','--jobs','1',*files]
 for attempt in range(3):
  result=subprocess.run(cmd,capture_output=True,text=True,encoding='utf-8')
  bad=[]
  for row in batch:
   olean=next(checked(windows(p)) for p in row['paths'] if p.endswith('.olean'))
   if not windows(row['file']).exists() or not olean.exists() or olean.stat().st_size==0:
    bad.append(row)
  if result.returncode==0 and not bad and not result.stderr.strip():break
  if not bad:bad=batch
  print(f'Refreshing {len(bad)} interrupted download(s) in batch {start}; attempt {attempt+1}',flush=True)
  for row in bad:
   archive=windows(row['file']);tmp=archive.with_suffix('.redownload')
   url='https://lakecache.blob.core.windows.net/mathlib4-master/f/'+archive.name
   fetch=subprocess.run(['curl.exe','--http1.1','--fail','--silent','--show-error','--max-time','90','--retry','2',url,'-o',str(tmp)],capture_output=True)
   if fetch.returncode:
    url='https://lakecache.blob.core.windows.net/mathlib4/f/'+archive.name
    subprocess.run(['curl.exe','--http1.1','--fail','--silent','--show-error','--max-time','90','--retry','2',url,'-o',str(tmp)],check=True)
   assert tmp.read_bytes()[:4] in {b'LTR3',b'LTR2',b'LTAR'}
   tmp.replace(archive)
 else:raise RuntimeError((start,result.stdout,result.stderr,bad))
 compress=[]
 for row in batch:
  paths=[checked(windows(p)) for p in row['paths']]
  olean=[p for p in paths if p.suffix=='.olean']
  assert len(olean)==1 and olean[0].exists() and olean[0].stat().st_size>0,row
  records={}
  for p in paths:
   if not p.exists():continue
   if p.name.endswith(('.c','.c.hash','.ilean','.ilean.hash')):
    p.unlink()
    continue
   records[str(p.relative_to(ML)).replace('\\','/')]=hashlib.sha256(p.read_bytes()).hexdigest()
   if p.stat().st_size>16384:compress.append(p)
  archive=windows(row['file'])
  receipt.append({'module':row['module'],'cache_file':archive.name,
   'cache_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'retained_files':records})
 for i in range(0,len(compress),60):
  c=subprocess.run(['compact.exe','/C','/F','/EXE:LZX','/I','/Q',*[str(p) for p in compress[i:i+60]]],capture_output=True)
  if c.returncode:raise RuntimeError(('compression',c.stdout.decode(errors='replace')))
 (W/'MATHLIB_ARTIFACT_RECEIPT.json').write_text(json.dumps({'status':'extracting','mathlib_revision':'360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56','modules':receipt},indent=2)+'\n',encoding='utf-8',newline='\n')
 # These download-cache copies are reproducible from the pinned source hashes.
 # Remove only the exact, successfully extracted and hash-recorded archives.
 for row in batch:
  archive=windows(row['file']);assert archive.is_relative_to(W/'mathlib-cache432');archive.unlink()
 print(f'Freshly extracted and hash-recorded {len(receipt)}/2145 modules; free={shutil.disk_usage(W).free//1024**2} MiB',flush=True)
value=json.loads((W/'MATHLIB_ARTIFACT_RECEIPT.json').read_text(encoding='utf-8'));value['status']='complete'
(W/'MATHLIB_ARTIFACT_RECEIPT.json').write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8',newline='\n')
print('Pinned selective Mathlib installation complete.',flush=True)
