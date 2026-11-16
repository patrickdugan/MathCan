from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

W=Path(__file__).resolve().parent
O=W.parent/'outputs'
R=W/'replay432/Decoder'
N=W/'replay435/Decoder'
env=dict(os.environ,CAMPAIGN_WORK=str(W))
commands=[]
for name,p in [('decoder_acceptance',W/'accept_decoder432.py'),
               ('decoder_acceptance_controls',W/'test_decoder_acceptance.py'),
               ('retained_spatial_acceptance',W/'accept_spatial432.py'),
               ('decoder_trace_fixture',W/'Compactification-Theory/research/quantization/decoder_trace_fixture.py')]:
    args=[sys.executable,str(p)]
    result=subprocess.run(args,capture_output=True,text=True,encoding='utf-8',env=env)
    (W/'logs'/f'{name}.log').write_text(result.stdout+result.stderr,encoding='utf-8',newline='\n')
    assert result.returncode==0,(name,result.stdout,result.stderr)
    commands.append({'name':name,'command':args,'exit_code':result.returncode})
A=json.loads((R/'ACCEPTANCE.json').read_text(encoding='utf-8'))
assert len(A['theorems'])==39 and A['verdicts']['unsupported']==A['verdicts']['rejected']==0
expected435=['bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38',
             '12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6']
assert [line.split()[0] for line in (N/'preserved_binary_hashes.txt').read_text().splitlines()]==expected435
for module in ['SentinelDecoder','DecodedJetCapture']:
    for stage in ['native','leanchecker']:
        assert 'error:' not in (N/f'{module}_{stage}.log').read_text(encoding='utf-8')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(W/'build/oxilean-verify')=='831e7ad751d69d7f27e8ee59ec40246a6256e971e11f418b0e92f9722771e9fa'
assert sha(W/'replay432/lean4export-source/.lake/build/bin/lean4export')=='e6580597a1482740114b5a1a05add574334a5eeaed5f4f5c9cd670e146859009'
old=json.loads((O/'FINAL_VALIDATION.json').read_text(encoding='utf-8'))
old['formal_theorems']=95
old['decoder_continuation']={'date':'2026-11-16','new_theorems':39,'native_versions':['4.32.0-rc1','preserved 4.35.0'],
    'native_and_leanchecker':'accepted in both environments','verdicts':A['verdicts'],
    'constants_compared':A['constants_compared'],'export_sha256':A['export_sha256'],
    'source_sha256':A['source_sha256'],'acceptance_tamper_controls':8,
    'trace_fixtures':json.loads((W/'Compactification-Theory/research/quantization/decoder_trace_fixture_results.json').read_text())}
old['executed_commands'].extend(commands)
old['full_theorem_scope']='Ordered-field spatial and exact/robust sentinel decoder semantics proved; full analytic approximation theorem and dense compiler/resource proof remain open.'
(O/'FINAL_VALIDATION.json').write_text(json.dumps(old,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'status':'passed','new_roots':39,'research_roots_total':95,
    'verdicts':A['verdicts'],'constants_compared':A['constants_compared'],'tamper_controls':8},indent=2))
