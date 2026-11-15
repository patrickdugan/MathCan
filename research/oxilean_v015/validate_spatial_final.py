from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

W=Path(__file__).resolve().parent
O=W.parent/'outputs'
env=dict(os.environ,CAMPAIGN_WORK=str(W))
runs=[]
for name,script in [('new_spatial_acceptance','accept_spatial432.py'),
                    ('spatial_acceptance_tamper_controls','test_spatial_acceptance.py'),
                    ('retained_hodge_acceptance','accept_hodge432.py'),
                    ('retained_14_lemma_acceptance','accept_research_lemmas432.py')]:
    args=[sys.executable,str(W/script)]
    p=subprocess.run(args,capture_output=True,text=True,encoding='utf-8',env=env)
    (W/'logs'/f'{name}.log').write_text(p.stdout+p.stderr,encoding='utf-8',newline='\n')
    assert p.returncode==0,(name,p.stdout,p.stderr)
    runs.append({'name':name,'command':args,'exit_code':p.returncode})
A=json.loads((W/'replay432/SpatialScalar/ACCEPTANCE.json').read_text(encoding='utf-8'))
assert len(A['theorems'])==42
assert A['verdicts']['unsupported']==A['verdicts']['rejected']==0
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(W/'build/oxilean-verify')=='831e7ad751d69d7f27e8ee59ec40246a6256e971e11f418b0e92f9722771e9fa'
assert sha(W/'replay432/lean4export-source/.lake/build/bin/lean4export')=='e6580597a1482740114b5a1a05add574334a5eeaed5f4f5c9cd670e146859009'
T=W/'toolchains/lean-4.32.0-rc1-linux/bin'
assert sha(T/'lean')=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert sha(T/'leanchecker')=='c7c51e296d28dd443ed60f9414feef41253ede89dea76dbb2adde29768c3ed5f'
expected435=['bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38',
             '12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6']
N=W/'replay435/SpatialFormalization'
assert [line.split()[0] for line in (N/'preserved_binary_hashes.txt').read_text().splitlines()]==expected435
for name in ['SpatialScalar','SpatialRouting','SpatialNormalized','SpatialClipped']:
    for kind in ['native','leanchecker']:
        assert 'error:' not in (N/f'{name}_{kind}.log').read_text(encoding='utf-8')
old=json.loads((O/'FINAL_VALIDATION.json').read_text(encoding='utf-8'))
assert sha(W/'Compactification-Theory/research/quantization/spatial_circuit.py')==old['spatial_source_sha256']
assert sha(W/'Compactification-Theory/research/quantization/test_spatial_circuit.py')==old['spatial_tests_sha256']
old['formal_theorems']=56
old['new_spatial_formalization']={'theorems':42,'native_432':'accepted','leanchecker_432':'accepted',
    'preserved_435':'all four modules compiled and leanchecker accepted; original binary hashes unchanged',
    'oxilean_verdicts':A['verdicts'],'constants_compared':A['constants_compared'],
    'export_sha256':A['export_sha256'],'tamper_controls':8,'source_sha256':A['source_sha256']}
old['full_theorem_scope']='Paper proof and explicit compiler; Lean now proves ordered-field safe spatial extraction and bounded capture. Analytic, decoder and dense compiler obligations remain open.'
old['executed_commands'].extend(runs)
(O/'FINAL_VALIDATION.json').write_text(json.dumps(old,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'status':'passed','new_theorems':42,'total_research_theorems':56,
                  'verdicts':A['verdicts'],'tamper_controls':8},indent=2))
