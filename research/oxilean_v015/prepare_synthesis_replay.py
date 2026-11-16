from pathlib import Path
import json,re,os
W=Path(os.environ.get('CAMPAIGN_WORK',Path(__file__).resolve().parent)).resolve();R=W/'replay432/Synthesis';R.mkdir(parents=True,exist_ok=True)
mods=['JetSynthesis','FrameSynthesis','MultivariateTaylor','MultivariateBounds','MultivariateHolder','SynthesisCapture','MultivariateCapture']
base=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib'
roots=['MathCan.'+m+'.'+n for m in mods for n in re.findall(r'^(?:theorem|lemma) (\w+)',(base/(m+'.lean')).read_text(encoding='utf-8'),re.M)]
assert len(roots)==len(set(roots))==47
manifest={'modules':['ApproximationMathlib.'+m for m in mods],
 'sources':{m:'research/approximation_mathlib432/ApproximationMathlib/'+m+'.lean' for m in mods},
 'theorems':roots,'mathlib_revision':'360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56','vendor_roots':[]}
(R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n');(R/'roots.txt').write_text('\n'.join(roots)+'\n',encoding='utf-8',newline='\n')
(R/'modules.txt').write_text('\n'.join(mods)+'\n',encoding='utf-8',newline='\n')
s=(W/'replay432/CompareLemmas.lean').read_text(encoding='utf-8').replace('import MathCan.QuantizedJet\nimport MathCan.SpatialInterface','import ApproximationMathlib.MultivariateCapture').replace('MathCan.SpatialInterface.capture_at_index','MathCan.MultivariateCapture.holder_decoded_approximation')
s+='\n'+'\n'.join('#print axioms '+n for n in roots)+'\n'
(R/'CompareSynthesis.lean').write_text(s,encoding='utf-8',newline='\n')
s='''import LeanChecker
open Lean
unsafe def runSynthesisKernelChecks : IO Unit := do
  initSearchPath (← findSysroot)
'''
s+='  for m in #['+', '.join('`ApproximationMathlib.'+m for m in mods)+'] do\n'
s+='''    IO.println s!"Checking {m} using pinned replayFromImports"
    replayFromImports m
    IO.println s!"Accepted {m}"
#eval runSynthesisKernelChecks
'''
(R/'DirectKernel.lean').write_text(s,encoding='utf-8',newline='\n')
print('Prepared',len(roots),'authored synthesis roots.')
