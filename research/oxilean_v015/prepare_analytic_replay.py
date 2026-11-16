from pathlib import Path
import json,re,os
W=Path(os.environ.get('CAMPAIGN_WORK',Path(__file__).resolve().parent)).resolve()
R=W/'replay432/Analytic';R.mkdir(parents=True,exist_ok=True)
base=W/'MathCan/research/approximation_mathlib432'
mods=['TaylorFoundation','SmoothTaylor','CapturedApproximation']
roots=[]
for m in mods:
 s=(base/'ApproximationMathlib'/f'{m}.lean').read_text(encoding='utf-8')
 roots+=['MathCan.'+m+'.'+n for n in re.findall(r'^(?:theorem|lemma) (\w+)',s,re.M)]
assert len(roots)==len(set(roots)) and roots
manifest={'modules':['ApproximationMathlib.'+m for m in mods],
 'sources':{m:'research/approximation_mathlib432/ApproximationMathlib/'+m+'.lean' for m in mods},
 'theorems':roots,'vendor_module':'ApproximationMathlib.TaylorFoundation',
 'mathlib_revision':'360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56'}
(R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
(R/'roots.txt').write_text('\n'.join(roots)+'\n',encoding='utf-8',newline='\n')
(R/'PrintAnalytic.lean').write_text('import ApproximationMathlib.CapturedApproximation\n'+
 '\n'.join('#print axioms '+n for n in roots)+'\n',encoding='utf-8',newline='\n')
s=(W/'replay432/CompareLemmas.lean').read_text(encoding='utf-8')
s=s.replace('import MathCan.QuantizedJet\nimport MathCan.SpatialInterface','import ApproximationMathlib.CapturedApproximation')
s=s.replace('MathCan.SpatialInterface.capture_at_index','MathCan.CapturedApproximation.decoded_smooth_approximation')
(R/'CompareAnalytic.lean').write_text(s,encoding='utf-8',newline='\n')
print('Prepared',len(roots),'analytic roots (including attributed upstream foundations).')

(R/"DirectKernel.lean").write_text('import LeanChecker\n\n/-! Native kernel replay through the unmodified pinned LeanChecker API.\nThis omits only the stock CLI\'s recursive scan of every olean search path. -/\nopen Lean\nunsafe def runAnalyticKernelChecks : IO Unit := do\n  initSearchPath (← findSysroot)\n  for m in #[`ApproximationMathlib.TaylorFoundation, `ApproximationMathlib.SmoothTaylor,\n      `ApproximationMathlib.CapturedApproximation] do\n    IO.println s!"Checking {m} with pinned LeanChecker.replayFromImports"\n    replayFromImports m\n    IO.println s!"Accepted {m}"\n#eval runAnalyticKernelChecks\n',encoding="utf-8",newline="\n")
(R/"CompareAnalyticWithAxioms.lean").write_text(s+"\n"+"\n".join("#print axioms "+n for n in roots)+"\n",encoding="utf-8",newline="\n")
