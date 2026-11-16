from pathlib import Path
import json
import os
import subprocess

W=Path(__file__).resolve().parent
O=W.parent/'outputs'
env=dict(os.environ,GIT_TERMINAL_PROMPT='0')
rows=[]
for name,owner,branch in [('MathCan','patrickdugan','research/quantized-jet-replay-20261115'),
                          ('Compactification-Theory','MoralityLabAI','research/quantization-d-audit-20261115')]:
    repo=W/name
    def git(*args):return subprocess.check_output(['git','-C',str(repo),*args],text=True,encoding='utf-8',env=env).strip()
    assert not git('status','--porcelain')
    assert git('branch','--show-current')==branch
    local=git('rev-parse','HEAD')
    url=git('remote','get-url','origin')
    assert url==f'https://github.com/{owner}/{name}.git'
    remote=git('ls-remote','--heads','origin','refs/heads/'+branch)
    parts=remote.split()
    assert parts==[local,'refs/heads/'+branch],remote
    rows.append({'repository':name,'repository_full_name':owner+'/'+name,'branch':branch,
        'local_commit':local,'remote_commit':parts[0],'remote_url':url,'verified':True,
        'url':f'https://github.com/{owner}/{name}/tree/{branch}',
        'commit_url':f'https://github.com/{owner}/{name}/commit/{local}',
        'verification_command':['git','ls-remote','--heads','origin','refs/heads/'+branch]})
receipt={'status':'verified','client_date':'2026-11-16','timezone':'Asia/Taipei',
    'authorization':'User explicitly requested pushing the research work.',
    'repositories':rows,'message_status':'No email, direct message or repository comment sent in the multivariate synthesis continuation.'}
(O/'PUSH_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(receipt,indent=2))
