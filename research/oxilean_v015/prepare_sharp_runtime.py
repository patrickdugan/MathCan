from pathlib import Path
import hashlib,json,shutil,time
W=Path(__file__).resolve().parent
R=W/'replay432/Sharp';R.mkdir(parents=True,exist_ok=True)
target=Path(r'\\wsl.localhost\Ubuntu\dev\shm\oxilean-sharp432-20261117')
target.mkdir(parents=True,exist_ok=True)
sources=[(W/'toolchains/lean-4.32.0-rc1-linux/lib/lean','toolchain-lib'),
         (W/'replay432/Synthesis/lib','lib')]
files=[]
for source,prefix in sources:
 for p in source.rglob('*'):
  if p.is_file() and any(p.name.endswith(ext) for ext in ['.olean','.olean.server','.olean.private','.ir','.ir.server','.ir.private']):
   files.append((p,Path(prefix)/p.relative_to(source)))
total=sum(p.stat().st_size for p,_ in files)
assert shutil.disk_usage(target).free>total+512*1024**2
print(f'Preparing {len(files)} unchanged runtime files ({total} bytes)',flush=True)
records={};started=time.monotonic()
for i,(source,relative) in enumerate(files,1):
 data=source.read_bytes();expected=hashlib.sha256(data).hexdigest();dest=target/relative
 assert dest.is_relative_to(target)
 dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists() or hashlib.sha256(dest.read_bytes()).hexdigest()!=expected:
  temporary=dest.with_name(dest.name+'.sharp-copy-tmp')
  temporary.write_bytes(data)
  assert hashlib.sha256(temporary.read_bytes()).hexdigest()==expected
  temporary.replace(dest)
 assert hashlib.sha256(dest.read_bytes()).hexdigest()==expected,str(relative)
 records[relative.as_posix()]=expected
 if i%500==0:print(f'Checked {i}/{len(files)} runtime files',flush=True)
result={'status':'matched','target_linux':'/dev/shm/oxilean-sharp432-20261117',
 'files':records,'bytes':total,'elapsed_seconds':time.monotonic()-started,
 'purpose':'Byte-identical copies of the existing pinned Lean runtime and accepted project oleans'}
(R/'runtime_mirror.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in result.items() if k!='files'},indent=2))
