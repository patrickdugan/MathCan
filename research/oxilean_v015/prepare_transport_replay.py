from pathlib import Path
import json
import os
import re

W=Path(os.environ.get('CAMPAIGN_WORK',Path(__file__).resolve().parent)).resolve()
R=W/'replay432/Transport'
R.mkdir(parents=True,exist_ok=True)
modules=['HammingSelector','TaylorPolynomial','TaylorTransport','TaylorFrame','ConcreteJetCapture']
roots=['MathCan.'+m+'.'+n for m in modules for n in re.findall(r'^theorem (\w+)',
    (W/'MathCan/MathCan'/f'{m}.lean').read_text(encoding='utf-8'),re.M)]
assert roots and len(roots)==len(set(roots))
(R/'manifest.json').write_text(json.dumps({'modules':['MathCan.'+m for m in modules],
    'theorems':roots},indent=2)+'\n',encoding='utf-8',newline='\n')
(R/'roots.txt').write_text('\n'.join(roots)+'\n',encoding='utf-8',newline='\n')
(R/'PrintTransport.lean').write_text('import MathCan.ConcreteJetCapture\n'+
    '\n'.join('#print axioms '+n for n in roots)+'\n',encoding='utf-8',newline='\n')
compare=(W/'replay432/CompareLemmas.lean').read_text(encoding='utf-8')
compare=compare.replace('import MathCan.QuantizedJet\nimport MathCan.SpatialInterface','import MathCan.ConcreteJetCapture')
compare=compare.replace('MathCan.SpatialInterface.capture_at_index','MathCan.ConcreteJetCapture.robust_concrete_spatial_capture')
(R/'CompareTransport.lean').write_text(compare,encoding='utf-8',newline='\n')
print(f'Prepared {len(roots)} Hamming/Taylor/capture theorem roots.')
