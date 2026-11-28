"""Reproduce CTS-13 in chunks; check all non-timing rows and independent certificates."""
import json, subprocess, sys
from pathlib import Path
import cts13 as c
root=Path(__file__).resolve().parent
for rep in (0,1):
    for start in (0,4,8):
        subprocess.run([sys.executable,str(root/'cts13.py'),'--start',str(start),'--end',str(start+4),'--repeat',str(rep),'--out',str(root/f'run{rep}_{start}.json')],check=True)
r=[[z for n in (0,4,8) for z in json.loads((root/f'run{i}_{n}.json').read_text())] for i in (0,1)]
assert c.b.stable(r[0])==c.b.stable(r[1])
c.p.old.dump(root/'results.json',r[0]);c.p.old.dump(root/'summary.json',c.summarize(r[0]));c.p.old.dump(root/'replay.json',{'identical':True,'records':len(r[0])*c.b.STEPS*len(c.ARMS),**c.summarize(r[1])})
c.p.old.dump(root/'audit.json',c.audit(r[0]));subprocess.run([sys.executable,str(root/'boundary_tests.py')],cwd=root,check=True);print('replay and audit passed')
