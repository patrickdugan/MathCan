"""Fetch only pinned source imports, verifying every file against Git blob IDs.
Uses the system HTTPS client with its normal certificate verification.
"""
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import hashlib
import json
import re
import subprocess

W=Path(__file__).resolve().parent
ROOT=W/'mathlib432-local'
REV='360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56'
URL='https://raw.githubusercontent.com/leanprover-community/mathlib4/'+REV+'/'
assert subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()==REV
tree=subprocess.check_output(['git','-c','core.quotePath=false','-C',str(ROOT),'ls-tree','-r','HEAD'],text=True,encoding='utf-8')
blobs={line.split('\t',1)[1]:line.split()[2] for line in tree.splitlines() if ' blob ' in line}
def verified(path):
    p=ROOT/path
    if not p.exists():return False
    data=p.read_bytes()
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blobs[path]
def fetch(path):
    assert path in blobs and not Path(path).is_absolute() and '..' not in Path(path).parts,path
    p=ROOT/path
    if not verified(path):
        p.parent.mkdir(parents=True,exist_ok=True)
        tmp=p.with_suffix(p.suffix+'.download')
        proc=subprocess.run(['curl.exe','--http1.1','--fail','--silent','--show-error','--max-time','90',
            '--retry','2',URL+path,'-o',str(tmp)],capture_output=True,text=True)
        if proc.returncode:raise RuntimeError((path,proc.stderr))
        data=tmp.read_bytes()
        actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert actual==blobs[path],(path,actual,blobs[path])
        tmp.replace(p)
    return path,p.read_text(encoding='utf-8')
roots=['lean-toolchain','lakefile.lean','lake-manifest.json','LICENSE']
roots += [p for p in blobs if p.startswith('Cache/') and p.endswith('.lean')]
roots += [m.replace('.','/')+'.lean' for m in [
    'Mathlib.Algebra.Polynomial.Module.Basic','Mathlib.Analysis.Calculus.ContDiff.Operations',
    'Mathlib.Analysis.Calculus.Deriv.MeanValue','Mathlib.Analysis.Calculus.Deriv.Pow',
    'Mathlib.Analysis.Calculus.IteratedDeriv.Defs','Mathlib.Tactic.Ring','Mathlib.Tactic.FieldSimp',
    'Mathlib.Tactic.GCongr','Mathlib.Tactic.FunProp','Mathlib.Analysis.SpecialFunctions.Pow.Real']]
seen=set();pending=set(roots);external=set()
with ThreadPoolExecutor(max_workers=12) as pool:
    while pending:
        batch=sorted(pending-seen)
        pending=set()
        jobs={pool.submit(fetch,p):p for p in batch}
        for future in as_completed(jobs):
            path,text=future.result();seen.add(path)
            for line in text.splitlines():
                m=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
                if not m:continue
                for module in m[1].split('--',1)[0].split():
                    if module in {'all'}:continue
                    if module.startswith('Mathlib.'):
                        dependency=module.replace('.','/')+'.lean'
                        if dependency not in seen:pending.add(dependency)
                    elif module.split('.',1)[0] not in {'Lean','Lake','Init','Std','Cache'}:
                        external.add(module)
        print(json.dumps({'verified_sources':len(seen),'next_batch':len(pending),'external_modules':len(external)}),flush=True)
receipt={'revision':REV,'tag':'v4.32.0-rc1','verified_git_blobs':{p:blobs[p] for p in sorted(seen)},
    'external_imports':sorted(external),'scope':'Selective sources for finite Taylor/mean-value calculus, excluding interval-integral Taylor imports.'}
(W/'MATHLIB_SOURCE_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
print('Pinned Mathlib source closure ready.',flush=True)
