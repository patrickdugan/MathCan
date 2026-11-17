from pathlib import Path
import gzip,hashlib,json,shutil
W=Path(__file__).resolve().parent;R=W/'replay432/Sharp';O=W.parent/'outputs'
M=W/'MathCan/research/oxilean_v015';C=W/'Compactification-Theory/research/quantization'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
A=json.loads((R/'ACCEPTANCE.json').read_text());manifest=json.loads((R/'manifest.json').read_text())
assert A['status']=='accepted' and len(A['theorems'])==len(manifest['theorems'])
assert A['verdicts']['unsupported']==A['verdicts']['rejected']==0
assert sha(R/'Lemmas.ndjson')==A['export_sha256']
count=len(A['theorems']);previous=json.loads((W/'replay432/Synthesis/VERIFICATION_SUMMARY.json').read_text())
total=previous['research_roots_total']+count
for name,number in [('acceptance_controls.log',15),('auditor_controls.log',7)]:
 text=(R/name).read_text();assert f'Ran {number} tests' in text and text.rstrip().endswith('OK')
for rel,digest in A['source_sha256'].items():assert sha(W/'MathCan'/rel)==digest
assert sha(W/'MathCan/MathCan/Hodge.lean')=='6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5'
pins={}
for line in (R/'binary_before.sha256').read_text().splitlines():
 digest,path=line.split('  ',1);p=Path(path)
 if not p.exists():p=W/path.split('/work/',1)[1]
 assert sha(p)==digest; pins[str(p.relative_to(W)).replace('\\','/')]=digest
receipt={'status':'passed','lean':'4.32.0-rc1','new_authored_roots':count,'research_roots_total':total,
 'source_sha256':A['source_sha256'],'binary_sha256':pins,'mathlib_revision':A['mathlib_revision'],
 'native_kernel_method':A['native_kernel_method'],
 'olean_sha256':{m:sha(R/'lib/ApproximationMathlib'/(m.rsplit('.',1)[-1]+'.olean')) for m in manifest['modules']},
 'mirror_receipts_sha256':{p.name:sha(p) for p in R.glob('*mirror*.json')},
 'prior_proofs':'All prior accepted source hashes, including synthesis, remain unchanged',
 'development':'Incremental language-server checks are excluded from final acceptance; separate frozen batch build required'}
(R/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
summary={k:A[k] for k in ['status','export_sha256','verdicts','constants_compared','source_sha256','mathlib_revision','native_kernel_method','standard_axioms']}
summary.update(new_authored_roots=count,research_roots_total=total,acceptance_tamper_controls=15,structural_auditor_controls=7,roots=manifest['theorems'])
(R/'VERIFICATION_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
target=M/'pinned432_sharp';target.mkdir(parents=True,exist_ok=True)
excluded={'lsp_diagnostics.json','lsp_progress.json','lsp_driver.log','lsp_stderr.log','runtime_prepare.log','SharpResidual_dev.log','mirrors_before.log','frozen_pipeline.log'}
for p in R.iterdir():
 if not p.is_file() or p.name in excluded or '_dev' in p.name or p.suffix not in ['.json','.log','.lean','.txt','.sha256','.ndjson','.exitcode']:continue
 if p.suffix=='.ndjson':
  dest=target/(p.name+'.gz')
  with p.open('rb') as src,dest.open('wb') as raw:
   with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as out:shutil.copyfileobj(src,out)
  with gzip.open(dest,'rb') as src:assert hashlib.file_digest(src,'sha256').hexdigest()==A['export_sha256']
 else:shutil.copyfile(p,target/p.name)
helpers=['sharp_env432.sh','freeze_sharp432.sh','build_sharp432.sh','kernel_sharp432.sh','export_sharp432.sh',
 'compare_sharp432.sh','prepare_sharp_replay.py','accept_sharp432.py','test_sharp_acceptance.py',
 'prepare_sharp_runtime.py','prepare_sharp_executable.py','check_sharp_mirrors.py','finalize_sharp_phase.py',
 'run_frozen_sharp432.sh','promote_sharp_results.py','update_sharp_status.py',
 'check_sharp_git_content.py','record_sharp_push_receipt.py','package_sharp_results.py']
for name in helpers:shutil.copyfile(W/name,M/name)
for name in ['ACCEPTANCE.json','BUILD_RECEIPT.json','VERIFICATION_SUMMARY.json']:
 shutil.copyfile(R/name,O/('SHARP_'+name))
for name in ['BUILD_RECEIPT.json','VERIFICATION_SUMMARY.json']:shutil.copyfile(R/name,C/('SHARP_'+name))
report=f'''# Sharp derivative-component residuals and bounded correction alphabets

{count} new authored theorem roots pass frozen Lean compilation, native kernel
replay and independent OxiLean replay. The research campaign now has {total}
roots, including the earlier 12 attributed upstream Taylor roots. Hodge remains
separate and unchanged.

## Analytic result

For a C^k function on R^d, derivative rank r, remaining degree m=k-r, and a
coordinate word w, let g_w(x)=D^r f(x)[e_w] and z_w=mu^r g_w/r!.
`SharpJet.sharp_jet_transport` proves the genuine analytic Taylor residual

`|z_w(a+h) - (mu^r/r!) Taylor_m(g_w,a,h)| / tau <= 2 H D^(k+alpha)`

when `mu>=0`, `tau>0`, `H>=0`, `||h||<=mu D`, `D>=1`, `alpha>=0`, and
`mu^(k+alpha)<=2 tau`, under a
Holder bound H on the original highest derivative D^k f along the segment.
All ranks are covered, including m=0, zero displacement and zero mu. The more
precise component bound retains `D^(m+alpha)/(r! m!)`. The top-rank case uses
the highest tensor's oscillation directly. No residual or mixed-partial oracle
is assumed in this analytic theorem. `iterated_derivative_difference` and
`component_derivative_difference` justify passing from the original derivative
tensor to the scalar component's derivatives.

## Correction frames and approximation

The matrix predictor amplifies an existing tau/2 coefficient error by at most
`A_D tau/2`, where `A_D=2^(k+1) D^k`. For true-jet residual at most `B tau`,
rounding yields corrections in [-N,N] whenever

`N >= B + A_D/2 + 1/2`, `D < 2^p`, `2 N < 2^a`.

This alphabet has no inverse-tau or stream-length factor when B is fixed.
`component_sharp_frame` uses the analytic common budget `B=2 H D^(k+alpha)`.
It explicitly requires equations identifying the selected component targets
and their analytic Taylor predictors with the chosen concrete matrix layout.
`sharp_frames` proves finite frame validity and exact reference updates.
`sharp_decoded_accuracy` connects the frames through the existing base-4
sentinel reader, Hamming amplitude selector and spatial capture, proving
tau/2 coefficient accuracy for every selected state.

`SharpCapture` connects the residual contract to the existing smooth and
Holder multivariate approximation bounds. Its coefficient accuracy is proved;
its true-jet matrix-residual contract remains an explicit hypothesis.
`HolderCapture.holder_decoded_approximation` fully instantiates the degree-zero
case in arbitrary dimension for a globally Holder function, with mesh-bounded
anchor increments, bounded samples and valid spatial sites. It requires no
residual, matrix-identity or coefficient-accuracy premise and gives
`|f(x)-capturedValue| <= H rho^alpha + tau/2`.

The general higher-order normalized, grouped-multiindex matrix identification
is still open. In particular, the new component estimate is not silently
claimed to close the residual contract for the previous unscaled canonical
coefficient stream. Physical mesh scaling, grouping multiplicities and the
corresponding evaluation rescaling must be aligned there. Closed-cube/domain
specialization, geometry and dense ReLU arithmetic/resource realization also
remain open. Exact real polynomial evaluation is used.

## Verification

* New authored roots: {count}; one frozen compilation unit, with five namespaces.
* Native kernel: unmodified pinned LeanChecker.replayFromImports API.
* OxiLean: {A['verdicts']['verified']} verified declarations; 0 unsupported; 0 rejected.
* Source/export: {A['constants_compared']} constants matched, including statement,
  value and universe parameters. Only metadata and the let optimization flag
  are normalized; expression equality respects Lean alpha equivalence.
* Closed, unambiguous dependency graph; no unsafe declarations or admissions.
* Native and exported axiom sets agree per new root and contain only
  propext, Quot.sound and Classical.choice.
* 15 acceptance tamper controls and 7 structural-auditor controls passed.
* All prior accepted source hashes and Hodge bytes remain intact.

Lean is 4.32.0-rc1; mathlib stays pinned at
360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56. Existing official cached artifacts
are validated; a full source rebuild of mathlib is not claimed. Existing
toolchain executables, shared libraries and runtime artifacts are copied
byte-for-byte to Linux-local caches and hash checked around replay. No new
software or mathlib modules are installed. Incremental server checks and
interrupted development attempts are excluded from acceptance.

Export SHA-256: `{A['export_sha256']}`.
The acceptance, build receipt and per-root verdicts record the exact scope.

## Local reproduction

Use the preserved pinned workspace dependencies. Recreate the mathlib RAM cache
with the preceding synthesis mirror helper if WSL has restarted. On Windows run
`prepare_sharp_runtime.py` and `prepare_sharp_executable.py`; these copy existing
artifacts and write checksum receipts. Validate the original mathlib tree into
`replay432/Sharp/mathlib_before.json`. In WSL run `check_sharp_mirrors.py before`
and `run_frozen_sharp432.sh`. The latter freezes the manifest, rebuilds the module
and writes completed replay/comparison results under the named RAM results path.
Validate mathlib again into `mathlib_after.json` and run the mirror checker with
`after`. On Windows run `promote_sharp_results.py`, `accept_sharp432.py` and
`test_sharp_acceptance.py`. The original mathlib source/cache receipts, pinned
toolchain and exporter paths are required; binaries and oleans are not bundled.
'''
for directory in [O,M,C]:(directory/'SHARP_TRANSPORT_REPORT.md').write_text(report,encoding='utf-8',newline='\n')
print(json.dumps({'new_roots':count,'research_roots_total':total,'export_sha256':A['export_sha256']}))
