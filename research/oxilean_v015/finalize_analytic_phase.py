from pathlib import Path
import gzip,hashlib,json,shutil
W=Path(__file__).resolve().parent;O=W.parent/'outputs';M=W/'MathCan/research/oxilean_v015';C=W/'Compactification-Theory/research/quantization';R=W/'replay432/Analytic'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,expected in {
 'toolchains/lean-4.32.0-rc1-linux/bin/lean':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 'toolchains/lean-4.32.0-rc1-linux/bin/leanchecker':'c7c51e296d28dd443ed60f9414feef41253ede89dea76dbb2adde29768c3ed5f',
 'replay432/lean4export-source/.lake/build/bin/lean4export':'e6580597a1482740114b5a1a05add574334a5eeaed5f4f5c9cd670e146859009',
 'build/oxilean-verify':'831e7ad751d69d7f27e8ee59ec40246a6256e971e11f418b0e92f9722771e9fa',
 'MathCan/MathCan/Hodge.lean':'6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5'
}.items(): assert sha(W/rel)==expected,rel
A=json.loads((R/'ACCEPTANCE.json').read_text(encoding='utf-8'));G=json.loads((W/'replay432/Common/ACCEPTANCE.json').read_text(encoding='utf-8'))
assert A['status']==G['status']=='accepted'
assert len(A['theorems'])==29 and len(G['theorems'])==23
for rel,h in A['source_sha256'].items():assert sha(W/'MathCan'/rel)==h
for phase in ['before','after']:
 binding=json.loads((R/f'mathlib_{phase}.json').read_text(encoding='utf-8'));assert binding['status']=='matched'
assert 'Ran 10 tests' in (R/'acceptance_controls.log').read_text(encoding='utf-8') and (R/'acceptance_controls.log').read_text(encoding='utf-8').rstrip().endswith('OK')
for m in ['TaylorFoundation','SmoothTaylor','CapturedApproximation']:
 for suffix in ['native.log','leanchecker.log']:
  text=(R/(m+'_'+suffix)).read_text(encoding='utf-8');assert 'error:' not in text and 'uses `sorry`' not in text
receipt={'status':'passed','lean':'4.32.0-rc1','mathlib_revision':A['mathlib_revision'],
 'new_authored_roots':17,'attributed_upstream_roots':12,'native_kernel_replay':'all three analytic modules accepted through the unmodified pinned replayFromImports API from the pinned LeanChecker module',
 'leanchecker_api_olean_sha256':sha(W/'toolchains/lean-4.32.0-rc1-linux/lib/lean/LeanChecker.olean'),
 'source_sha256':A['source_sha256'],'olean_sha256':{p.name:sha(p) for p in (R/'lib/ApproximationMathlib').iterdir() if p.is_file()},
 'compiler_binary_sha256':sha(W/'toolchains/lean-4.32.0-rc1-linux/bin/lean'),
 'leanchecker_binary_sha256':sha(W/'toolchains/lean-4.32.0-rc1-linux/bin/leanchecker'),
 'exporter_binary_sha256':sha(W/'replay432/lean4export-source/.lake/build/bin/lean4export'),
 'oxilean_binary_sha256':sha(W/'build/oxilean-verify'),
 'mathlib_source_receipt_sha256':sha(W/'MATHLIB_SOURCE_RECEIPT.json'),
 'mathlib_package_receipt_sha256':sha(W/'MATHLIB_PACKAGE_RECEIPT.json'),
 'mathlib_artifact_receipt_sha256':sha(W/'MATHLIB_ARTIFACT_RECEIPT.json')}
(R/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
target=M/'pinned432_analytic';target.mkdir(parents=True,exist_ok=True)
def copy(p,dest):
 dest.parent.mkdir(parents=True,exist_ok=True)
 if p.suffix=='.ndjson':
  with p.open('rb') as src, dest.with_suffix('.ndjson.gz').open('wb') as raw:
   with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as out:shutil.copyfileobj(src,out)
 else:shutil.copyfile(p,dest)
for p in R.iterdir():
 if not p.is_file() or p.name.startswith(('real_smoke','RealSmoke')):continue
 if p.suffix in {'.json','.log','.lean','.txt','.ndjson','.sha256'}:copy(p,target/p.name)
diag=target/'real_foundation_smoke';diag.mkdir(exist_ok=True)
for p in R.iterdir():
 if p.is_file() and p.name.startswith(('real_smoke','RealSmoke')):copy(p,diag/p.name)
for name in ['MATHLIB_SOURCE_RECEIPT.json','MATHLIB_PACKAGE_RECEIPT.json','MATHLIB_ARTIFACT_RECEIPT.json']:
 shutil.copyfile(W/name,target/name)
for name in ['check_analytic432.sh','run_analytic_replay432.sh','direct_analytic_kernel432.sh','export_analytic_only432.sh','finish_analytic_replay432.sh','prepare_analytic_replay.py',
 'accept_analytic432.py','test_analytic_acceptance.py','validate_mathlib432.py',
 'SelectiveCache432.lean','run_mathlib_selective432.sh','fetch_mathlib_sources.py',
 'fetch_mathlib_packages.py','prepare_sparse_indices.py','extract_mathlib_batched.py',
 'smoke_mathlib_oxilean432.sh','finalize_analytic_phase.py','package_common_taylor_results.py']:
 shutil.copyfile(W/name,M/name)
report=f'''# Common gate bound and genuine scalar Taylor remainders

2026-11-16, Asia/Taipei. This continuation adds **40 authored theorem roots**
and replays **12 attributed Mathlib foundation roots** under new names. Together
with the preceding 158 roots, there are **210 research roots**; the unchanged
Hodge root remains separate. The full multivariate network approximation theorem
remains open.

## Mathematical results

The 23 core roots in CommonGateBound/CommonGateCapture prove
A_D=2^(k+1)*D^k for D>=1 and an injective layout of coordinate degrees at most k.
Each compatible fibre has at most one entry per axis degree. Filtering the row,
then applying the hockey-stick identity, proves the bound without a matrix-norm
assumption. All candidates with input bound C use the same gate constant C*A_D;
C=2 gives 2*A_D, independently of the number of streamed spatial sites.
The actual Hamming-selected update, packed scheduled recurrence, and exact/robust
spatial capture are connected using that common constant.

The isolated Mathlib project proves 17 authored analytic roots:

* C^(n+1) regularity and |D^(n+1)f|<=M on the closed interval give
  |f(x)-T_n(a,x)| <= M*|x-a|^(n+1)/(n+1)!.
* For k=n+1>=1, C^k regularity and a highest-derivative Hoelder bound with
  constant H and exponent alpha>=0 give
  |f(x)-T_k(a,x)| <= H*|x-a|^(k+alpha)/k!.
  Degree-zero Hoelder functions and coincident endpoints are also covered.
* With s=k+alpha, mu>=0, tau>0, |q|<=D and mu^s<=2*tau, the normalized
  remainder at a+mu*q is bounded by 2*H*D^s/k!.
* The core Horner coefficient list is proved equal to the analytic Taylor
  polynomial. Coordinate errors eta_i contribute at most sum eta_i*|h|^i;
  uniform errors epsilon cost at most J*epsilon when |h|<=1.
* decoded_holder_uniform_approximation substitutes the actual common-bound
  Hamming/sentinel/spatial capture vector into the approximation estimate,
  giving H*rho^s/k! + J*epsilon for rho<=1.

The analytic premises are actual ContDiffOn, within-interval derivatives and
Hoelder inequalities, rather than an assumed Taylor-remainder conclusion.
The final capture theorem retains an explicit coefficient-accuracy contract for
the concrete reference recurrence. Derivatives are taken within the pointwise
anchor/query interval. Identifying these coefficients with fixed-domain and
multivariate jets, constructing valid correction frames with the required accuracy,
deriving the geometric schedule/canonical layout, and proving the dense ReLU
arithmetic/resource compiler remain required for the full approximation theorem.
The scalar evaluator still uses exact real multiplication; its realization by an
approximate ReLU arithmetic circuit is not proved in this stage.

## Independent verification

| Corpus | Roots | Verified declarations | Unsupported | Rejected | Native constants matched |
|---|---:|---:|---:|---:|---:|
| Common bound/capture | 23 | {G['verdicts']['verified']} | 0 | 0 | {G['constants_compared']} |
| Analytic Taylor/capture, including 12 upstream roots | 29 | {A['verdicts']['verified']} | 0 | 0 | {A['constants_compared']} |

Every declaration verdict is checked, not just the process exit code. Every
exported type, proof/definition value and universe-parameter list matches the
native imported environment; only metadata and the nondependent-let flag are
normalized. Dependency graphs are closed and name-unambiguous. Native and exported
axiom inventories agree root by root and contain only propext, Quot.sound and
Classical.choice. There are no admitted proofs or added mathematical axioms.
Eight common-bound and ten analytic acceptance tamper controls pass. The concrete
real-number diagnostic separately verifies 4,524 declarations with no unsupported
or rejected declarations.

Lean 4.32.0-rc1 compilation and native kernel replay pass for all five new modules.
For the three analytic modules, the driver calls the unmodified pinned
replayFromImports API from the pinned LeanChecker module directly, omitting only the stock CLI search-path
scan. The stock analytic CLI run was interrupted by a WSL restart and is not
counted as successful. DirectKernel.lean and direct_kernel.log record the resumed
checks. The two core modules use the stock leanchecker CLI.
The two core modules also pass preserved Lean 4.35 and leanchecker. The analytic
modules use the isolated 4.32 Mathlib project; no 4.35 analytic replay is claimed.
All preceding proof sources retain their accepted hashes.

Common export SHA-256: `{G['export_sha256']}`.
Analytic export SHA-256: `{A['export_sha256']}`.

Mathlib is pinned to 360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
(v4.32.0-rc1). The selective installation has 1,906 Git-blob-verified Mathlib/helper
sources, eight manifest-pinned packages, and 2,145 cached build modules with 19,305
retained artifact hashes checked before and after replay. Official cache artifacts
are used; the full Mathlib library is not rebuilt from source. The dependency-closed
exported proof terms are independently checked. Regenerable C/editor-index files
are omitted locally, and retained files are compressed without changing content.
The earlier full-disk extraction failed and was discarded as installation evidence;
every required archive was subsequently freshly extracted and hash-recorded.

TaylorFoundation is a namespaced, attributed subset of the pinned upstream Taylor
module, with unchanged proof bodies, direct tactic imports and no interval-integral
imports. It is covered by the included Apache-2.0 license and source provenance.

## Reproduction and remaining program

Restore the included helper scripts into CAMPAIGN_WORK. Use the pinned local
Lean/exporter/OxiLean builds, restore the recorded Mathlib dependency, then run
run_common_replay432.sh, check_common435.sh, run_analytic_replay432.sh and the two
acceptance-control suites. Large analytic NDJSON exports are stored as deterministic
gzip files; decompress into replay432/Analytic/Lemmas.ndjson for offline audit.
The receipts bind all current proof sources, dependency artifacts and tool binaries.

For looped-layer experiments, the common gate and normalized remainder constants
supply concrete register ranges and correction budgets to test or enforce during
training. These are invariants of the specified decoder, not empirical evidence
that a trained transformer implements it. No new transformer performance claim is
made by this formalization.
'''
for path in [M/'COMMON_TAYLOR_FORMALIZATION_REPORT.md',C/'COMMON_TAYLOR_FORMALIZATION_REPORT.md',O/'COMMON_TAYLOR_FORMALIZATION_REPORT.md']:
 path.write_text(report,encoding='utf-8',newline='\n')
for path in [M/'README.md',C/'LEAN_FORMALIZATION_STATUS.md']:
 intro='Taylor-analysis continuation (2026-11-16): 40 authored roots and 12 attributed\nupstream roots now establish common gates, genuine scalar Taylor remainders,\nand decoded capture approximation bounds. All 210 research roots have replay\nevidence. Read COMMON_TAYLOR_FORMALIZATION_REPORT.md for exact scope and open work.\n\n'
 path.write_text(intro+path.read_text(encoding='utf-8'),encoding='utf-8',newline='\n')
old=json.loads((O/'FINAL_VALIDATION.json').read_text(encoding='utf-8'))
old['formal_theorems']=210
old['native_coverage']={'4.32.0-rc1':'all 210 research roots',
 'preserved 4.35.0':'181 core roots, including the two new common-bound modules; excludes the isolated Mathlib analysis'}
old['common_taylor_continuation']={'status':'passed','new_authored_roots':40,'attributed_upstream_roots':12,
 'common_verdicts':G['verdicts'],'analytic_verdicts':A['verdicts'],'common_export_sha256':G['export_sha256'],
 'analytic_export_sha256':A['export_sha256'],'acceptance_tamper_controls':{'common':8,'analytic':10},
 'mathlib_revision':A['mathlib_revision'],'analytic_native_version':'4.32.0-rc1'}
old['full_theorem_scope']='Common transport gate bound, exact/robust decoded spatial capture, genuine scalar Taylor/Hoelder remainders and coefficient-error approximation bounds proved. Fixed-domain/multivariate jet synthesis, geometric schedule and dense arithmetic/resource compiler remain open.'
for dest in [O/'FINAL_VALIDATION.json',M/'FINAL_VALIDATION.json',C/'FINAL_VALIDATION.json']:
 dest.write_text(json.dumps(old,indent=2)+'\n',encoding='utf-8',newline='\n')
for name in ['ACCEPTANCE.json','BUILD_RECEIPT.json']:
 shutil.copyfile(R/name,O/('ANALYTIC_'+name))
print(json.dumps({'status':'prepared','research_roots':210,'authored_new':40,'attributed_new':12,'analytic_verdicts':A['verdicts']},indent=2))
