from pathlib import Path
import os
import json
import re

W = Path(os.environ.get('CAMPAIGN_WORK', Path(__file__).resolve().parent))
R = W / 'replay432/SpatialScalar'
R.mkdir(parents=True, exist_ok=True)
modules = ['SpatialScalar', 'SpatialRouting', 'SpatialNormalized', 'SpatialClipped']
names = ['MathCan.'+module+'.'+n for module in modules for n in re.findall(
    r'^theorem (\w+)', (W/'MathCan/MathCan'/f'{module}.lean').read_text(encoding='utf-8'), re.M)]
assert names and len(names) == len(set(names))
(R/'roots.txt').write_text('\n'.join(names)+'\n', encoding='utf-8', newline='\n')
(R/'manifest.json').write_text(json.dumps({'modules':['MathCan.'+m for m in modules],'theorems':names}, indent=2)+'\n', encoding='utf-8', newline='\n')
(R/'PrintSpatial.lean').write_text('import MathCan.SpatialClipped\n'+'\n'.join('#print axioms '+n for n in names)+'\n', encoding='utf-8', newline='\n')
compare = (W/'replay432/CompareLemmas.lean').read_text(encoding='utf-8')
compare = compare.replace('import MathCan.QuantizedJet\nimport MathCan.SpatialInterface', 'import MathCan.SpatialClipped')
compare = compare.replace('MathCan.SpatialInterface.capture_at_index', 'MathCan.SpatialClipped.safe_spatial_stream')
(R/'CompareSpatial.lean').write_text(compare, encoding='utf-8', newline='\n')
print(f'Prepared {len(names)} theorem roots.')
