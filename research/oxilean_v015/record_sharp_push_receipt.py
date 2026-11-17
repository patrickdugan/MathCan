from pathlib import Path
import json,os,subprocess
W=Path(__file__).resolve().parent;O=W.parent/'outputs';rows=[]
env=dict(os.environ,GIT_TERMINAL_PROMPT='0')
content=json.loads((O/'SHARP_GIT_CONTENT_VERIFICATION.json').read_text());assert content['status']=='matched'
for name,owner,branch in [('MathCan','patrickdugan','research/quantized-jet-replay-20261115'),('Compactification-Theory','MoralityLabAI','research/quantization-d-audit-20261115')]:
 repo=W/name
 def git(*a):return subprocess.check_output(['git','-C',str(repo),*a],env=env,text=True).strip()
 assert not git('status','--porcelain') and git('branch','--show-current')==branch
 head=git('rev-parse','HEAD');assert head==content['repository_heads'][name]
 url=git('remote','get-url','origin');assert url==f'https://github.com/{owner}/{name}.git'
 remote=git('ls-remote','--heads','origin','refs/heads/'+branch).split();assert remote==[head,'refs/heads/'+branch]
 rows.append({'repository':name,'branch':branch,'local_commit':head,'remote_commit':head,'verified':True,
  'remote_url':url,'commit_url':f'https://github.com/{owner}/{name}/commit/{head}'})
receipt={'status':'verified','client_date':'2026-11-17','timezone':'Asia/Taipei','repositories':rows,
 'authorization':'User explicitly requested pushing verified work.','message_status':'No email, direct message or repository comment sent in this sharp transport continuation.'}
for name in ['PUSH_RECEIPT.json','SHARP_PUSH_RECEIPT.json']:(O/name).write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(receipt,indent=2))
