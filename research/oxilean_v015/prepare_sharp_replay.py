from pathlib import Path
import json,re,os,hashlib
W=Path(os.environ.get('CAMPAIGN_WORK',Path(__file__).resolve().parent)).resolve();R=W/'replay432/Sharp';R.mkdir(parents=True,exist_ok=True)
mods=['SharpTransport']
base=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib'
blocks=re.findall(r'^namespace (MathCan\.\w+)\n(.*?)^end \1\s*$',(base/'SharpTransport.lean').read_text(encoding='utf-8'),re.M|re.S)
assert len(blocks)==5
roots=[ns+'.'+n for ns,body in blocks for n in re.findall(r'^(?:theorem|lemma) (\w+)',body,re.M)]
assert len(roots)==len(set(roots)) and len(roots)>=20
manifest={'modules':['ApproximationMathlib.'+m for m in mods],
 'sources':{m:'research/approximation_mathlib432/ApproximationMathlib/'+m+'.lean' for m in mods},
 'theorems':roots,'mathlib_revision':'360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56','vendor_roots':[]}
for name,value in [('manifest.json',json.dumps(manifest,indent=2)),('roots.txt','\n'.join(roots)),('modules.txt','\n'.join(mods))]:
 (R/name).write_text(value+'\n',encoding='utf-8',newline='\n')
s=(W/'replay432/CompareLemmas.lean').read_text(encoding='utf-8').replace('import MathCan.QuantizedJet\nimport MathCan.SpatialInterface','import ApproximationMathlib.SharpTransport').replace('MathCan.SpatialInterface.capture_at_index','MathCan.HolderCapture.holder_decoded_approximation')
s+='\n'+'\n'.join('#print axioms '+n for n in roots)+'\n'
(R/'CompareSharp.lean').write_text(s,encoding='utf-8',newline='\n')
s='''import LeanChecker
open Lean
unsafe def runSharpKernelChecks : IO Unit := do
  initSearchPath (← findSysroot)
'''
s+='  for m in #['+', '.join('`ApproximationMathlib.'+m for m in mods)+'] do\n'
s+='''    IO.println s!"Checking {m} using pinned replayFromImports"
    replayFromImports m
    IO.println s!"Accepted {m}"
#eval runSharpKernelChecks
'''
(R/'DirectKernel.lean').write_text(s,encoding='utf-8',newline='\n')
print('Prepared',len(roots),'authored sharp residual/alphabet roots.')
