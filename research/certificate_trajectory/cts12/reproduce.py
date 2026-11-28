"""Replay two randomized policy orders and independently check the certificates."""
import json, subprocess, sys
from pathlib import Path
import cts12 as c
root=Path(__file__).resolve().parent
for rep in (0,1):
    for start in (0,4,8):
        subprocess.run([sys.executable,str(root/'cts12.py'),'--start',str(start),'--end',str(start+4),'--repeat',str(rep),'--out',str(root/f'run{rep}_{start}.json')],check=True)
r=[[z for n in (0,4,8) for z in json.loads((root/f'run{i}_{n}.json').read_text())] for i in (0,1)]
assert c.prev.stable(r[0])==c.prev.stable(r[1])
c.old.dump(root/'results.json',r[0]);c.old.dump(root/'summary.json',c.summarize(r[0]));c.old.dump(root/'replay.json',{'identical':True,'records':len(r[0])*c.prev.STEPS*len(c.ARMS),**c.summarize(r[1])})
c.old.dump(root/'audit.json',c.audit(r[0]));print('replay and audit passed',flush=True)
