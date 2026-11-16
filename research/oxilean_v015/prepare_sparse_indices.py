from pathlib import Path
import json,subprocess
W=Path(__file__).resolve().parent;root=W/'mathlib432-local'
for repo in [root]+[root/'.lake/packages'/x for x in json.loads((root/'lake-manifest.json').read_text())['packages'] for x in [x['name']]]:
 def run(args,data=None):
  return subprocess.check_output(['git','-C',str(repo),*args],input=data)
 run(['read-tree','HEAD'])
 paths=run(['ls-tree','-rz','--name-only','HEAD']).split(b'\0')
 missing=[p for p in paths if p and not (repo/p.decode()).exists()]
 if missing:run(['update-index','--skip-worktree','-z','--stdin'],b'\0'.join(missing)+b'\0')
 print(repo.name,len(paths)-1,'tracked;',len(missing),'omitted',flush=True)
