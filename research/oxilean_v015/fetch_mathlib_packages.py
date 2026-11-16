from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import hashlib,json,subprocess
W=Path(__file__).resolve().parent
M=W/'mathlib432-local'
manifest=json.loads((M/'lake-manifest.json').read_text(encoding='utf-8'))
base=M/'.lake/packages';base.mkdir(parents=True,exist_ok=True)
def run(args,cwd=None):
 p=subprocess.run(args,cwd=cwd,text=True,capture_output=True,encoding='utf-8',timeout=180)
 if p.returncode:raise RuntimeError((args,p.stdout,p.stderr))
 return p.stdout
jobs=[];receipts={}
for pkg in manifest['packages']:
 name=pkg['name'];root=base/name;rev=pkg['rev'];url=pkg['url']
 root.mkdir(parents=True,exist_ok=True)
 if not (root/'.git').exists():
  run(['git','init','--quiet',str(root)])
  run(['git','remote','add','origin',url],root)
  run(['git','config','remote.origin.promisor','true'],root)
  run(['git','config','remote.origin.partialclonefilter','blob:none'],root)
 try:head=run(['git','rev-parse','HEAD'],root).strip()
 except RuntimeError:head=None
 if head!=rev:
  print('Fetching pinned metadata: '+name,flush=True)
  run(['git','-c','http.version=HTTP/1.1','fetch','--quiet','--depth=1','--filter=blob:none','origin',rev],root)
  run(['git','update-ref','HEAD',rev],root)
 run(['git','config','core.autocrlf','false'],root)
 tree=run(['git','-c','core.quotePath=false','ls-tree','-r','HEAD'],root)
 blobs={line.split('\t',1)[1]:line.split()[2] for line in tree.splitlines() if ' blob ' in line}
 selected={p:b for p,b in blobs.items() if p.endswith(('.lean','.toml')) or p in {'lake-manifest.json','lean-toolchain','LICENSE','LICENSE.md'}}
 receipts[name]={'url':url,'revision':rev,'git_blobs':selected}
 raw=url.removesuffix('.git').replace('https://github.com/','https://raw.githubusercontent.com/')+'/'+rev+'/'
 jobs += [(root,p,b,raw+p) for p,b in selected.items()]
def fetch(item):
 root,p,b,url=item;target=root/p
 def valid(path):
  if not path.exists():return False
  data=path.read_bytes()
  return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==b
 if not valid(target):
  target.parent.mkdir(parents=True,exist_ok=True)
  tmp=target.with_suffix(target.suffix+'.download')
  run(['curl.exe','--http1.1','--fail','--silent','--show-error','--max-time','90','--retry','2',url,'-o',str(tmp)])
  assert valid(tmp),(p,b)
  tmp.replace(target)
 return p
print(f'Verifying {len(jobs)} dependency source files.',flush=True)
with ThreadPoolExecutor(max_workers=12) as pool:
 for i,f in enumerate(as_completed([pool.submit(fetch,j) for j in jobs]),1):
  f.result()
  if i%100==0:print(f'{i}/{len(jobs)} verified',flush=True)
(W/'MATHLIB_PACKAGE_RECEIPT.json').write_text(json.dumps(receipts,indent=2)+'\n',encoding='utf-8',newline='\n')
print('All pinned package sources ready.',flush=True)
