from pathlib import Path
import json
import os
import re

W=Path(os.environ.get('CAMPAIGN_WORK',Path(__file__).resolve().parent)).resolve()
R=W/'replay432/Common'
R.mkdir(parents=True,exist_ok=True)
modules=['CommonGateBound','CommonGateCapture']
roots=['MathCan.'+m+'.'+n for m in modules for n in re.findall(r'^theorem (\w+)',
    (W/'MathCan/MathCan'/f'{m}.lean').read_text(encoding='utf-8'),re.M)]
assert roots and len(roots)==len(set(roots))
(R/'manifest.json').write_text(json.dumps({'modules':['MathCan.'+m for m in modules],
    'theorems':roots},indent=2)+'\n',encoding='utf-8',newline='\n')
(R/'roots.txt').write_text('\n'.join(roots)+'\n',encoding='utf-8',newline='\n')
(R/'PrintCommon.lean').write_text('import MathCan.CommonGateCapture\n'+
    '\n'.join('#print axioms '+n for n in roots)+'\n',encoding='utf-8',newline='\n')
compare=(W/'replay432/CompareLemmas.lean').read_text(encoding='utf-8')
compare=compare.replace('import MathCan.QuantizedJet\nimport MathCan.SpatialInterface','import MathCan.CommonGateCapture')
compare=compare.replace('MathCan.SpatialInterface.capture_at_index','MathCan.CommonGateCapture.robust_common_spatial_capture')
(R/'CompareCommon.lean').write_text(compare,encoding='utf-8',newline='\n')
print(f'Prepared {len(roots)} Hamming/Taylor/capture theorem roots.')
