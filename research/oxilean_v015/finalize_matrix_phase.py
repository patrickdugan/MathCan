from pathlib import Path
import gzip,hashlib,json,shutil
W=Path(__file__).resolve().parent;R=W/'replay432/Matrix';O=W.parent/'outputs'
M=W/'MathCan/research/oxilean_v015';C=W/'Compactification-Theory/research/quantization'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
A=json.loads((R/'ACCEPTANCE.json').read_text(encoding='utf-8'));manifest=json.loads((R/'manifest.json').read_text(encoding='utf-8'))
assert A['status']=='accepted' and len(A['theorems'])==34 and A['verdicts']['unsupported']==A['verdicts']['rejected']==0
assert sha(R/'Lemmas.ndjson')==A['export_sha256']
for name,count in [('acceptance_controls.log',18),('auditor_controls.log',7)]:
 t=(R/name).read_text(encoding='utf-8');assert f'Ran {count} tests' in t and t.rstrip().endswith('OK')
for rel,digest in A['source_sha256'].items():assert sha(W/'MathCan'/rel)==digest
assert sha(W/'MathCan/MathCan/Hodge.lean')=='6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5'
pins={}
for line in (R/'binary_before.sha256').read_text(encoding='utf-8').splitlines():
 digest,path=line.split('  ',1);p=W/path.split('/work/',1)[1];assert sha(p)==digest;pins[p.relative_to(W).as_posix()]=digest
total=json.loads((W/'replay432/Sharp/VERIFICATION_SUMMARY.json').read_text(encoding='utf-8'))['research_roots_total']+34
receipt={'status':'passed','lean':'4.32.0-rc1','new_authored_roots':34,'research_roots_total':total,
 'source_sha256':A['source_sha256'],'binary_sha256':pins,'mathlib_revision':A['mathlib_revision'],
 'native_kernel_method':A['native_kernel_method'],'source_mirror_sha256':sha(R/'source_mirror.json'),
 'olean_sha256':{'ApproximationMathlib.WordTransport':sha(R/'lib/ApproximationMathlib/WordTransport.olean')},
 'mirror_receipts_sha256':{p.name:sha(p) for p in R.glob('*mirror*.json')},
 'scope':'Ordered tensor-word representation. Compatibility, sharp residuals and decoded approximation are proved without a matrix or coefficient-accuracy hypothesis.'}
(R/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
summary={k:A[k] for k in ['status','export_sha256','verdicts','constants_compared','source_sha256','mathlib_revision','native_kernel_method','standard_axioms']}
summary.update(new_authored_roots=34,research_roots_total=total,acceptance_tamper_controls=18,structural_auditor_controls=7,roots=manifest['theorems'])
(R/'VERIFICATION_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8',newline='\n')
target=M/'pinned432_matrix';target.mkdir(parents=True,exist_ok=True)
for p in R.iterdir():
 if not p.is_file() or p.name.startswith('lsp_') or p.suffix not in ['.json','.log','.lean','.txt','.sha256','.ndjson']:continue
 if p.suffix=='.ndjson':
  dest=target/(p.name+'.gz')
  with p.open('rb') as src,dest.open('wb') as raw:
   with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as out:shutil.copyfileobj(src,out)
  with gzip.open(dest,'rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==A['export_sha256']
 else:shutil.copyfile(p,target/p.name)
helpers=['prepare_matrix_replay.py','matrix_env432.sh','run_matrix432.sh','check_matrix_mirrors.py','accept_matrix432.py',
 'test_matrix_acceptance.py','promote_matrix_results.py','finalize_matrix_phase.py','check_matrix_git_content.py',
 'record_matrix_push_receipt.py','package_matrix_results.py']
for name in helpers:shutil.copyfile(W/name,M/name)
for name in ['ACCEPTANCE.json','BUILD_RECEIPT.json','VERIFICATION_SUMMARY.json']:shutil.copyfile(R/name,O/('MATRIX_'+name))
for name in ['BUILD_RECEIPT.json','VERIFICATION_SUMMARY.json']:shutil.copyfile(R/name,C/('MATRIX_'+name))
report=f'''# General normalized multivariate jet matrix compatibility

34 authored roots pass frozen Lean compilation, native kernel replay and OxiLean.
The campaign now has {total} roots, including the earlier 12 attributed upstream
Taylor roots; Hodge remains separate and unchanged.

## Representation and compatibility

The new concrete realization stores ordered derivative words, with
`J=sum_(r=0)^k d^r` registers (`size_formula`). A word w of length r stores
`z_w(a)=mu^r/r! D^r f(a)[e_w]`. Directional order is retained in the registers.
This is a different finite layout from the earlier grouped multiindex layout;
its width depends only on fixed dimension and degree.

For an axis j and signed step q the row is explicitly

`(T_(j,q) z)_w = sum_(t=0)^(k-r) choose(t+r,r) q^t z_(j^t ++ w)`.

`matrix_application` identifies this formula with multiplication by the defined
J-by-J matrix; `matrix_integral` proves integer entries for integer q.
`directional_component` and `directional_ofFn` identify recursively defined
directional derivatives with genuine Frechet derivative tensor components.
`factorial_transport` supplies the normalization identity. Consequently
`matrix_compatibility` proves, for every dimension, order, coordinate, anchor,
mu and q, that the matrix predictor is the degree-(k-r) analytic Taylor
polynomial of the rank-r component at displacement `mu*q*e_j`, scaled by
`mu^r/r!`. There is no compatibility or mixed-partial symmetry premise.

The matrix has the existing common bound `A_D=2^(k+1) D^k` for `|q|<=D`,
D>=1. `matrix_residual` derives the common normalized residual
`|z_w(a+mu*q*e_j)-(T_(j,q)z(a))_w| <= 2 H D^(k+alpha) tau`
from C^k regularity, a Holder bound H on the original highest derivative,
mu>=0, alpha>=0, tau>0 and `mu^(k+alpha)<=2 tau`. All ranks, including the
degree-zero top component, and zero displacements are covered.

## Decoding and approximation

Motion tags encode axis, sign and bounded integer magnitude into a finite
alphabet. The actual Hamming selector reads these tags, and each packet also
contains the rounded signed corrections. All packets are concatenated into
the existing base-4 sentinel word. The decoded clipped recurrence and spatial
capture are proved to reproduce the synthesized reference trajectory.

`targets_residuals` discharges the true-jet residual contract for the recursively
constructed physical anchors. Corrections are bounded by

`N >= 2 H D^(k+alpha) + A_D/2 + 1/2`.

Thus N is independent of mu, tau and stream length. The motion and correction
bit widths obey `tagCount(d,D)<2^p` and `2N<2^a`; `finite_parameters` proves
finite choices exist. With mu<=1 and derivative tensors bounded by M at the
anchors, every true word coefficient is in [-M,M]. Rounding and clipping then
prove tau/2 accuracy for every reference state and for the selected decoded jet.

`evaluation_values` proves that evaluating the normalized true word jet at
`(x-a)/mu` gives the genuine multivariate Taylor polynomial. For k>=1, mu>0,
query distance at most rho<=mu, and the explicit regularity, boundedness,
safe-site and schedule-length conditions, `WordCapture.decoded_approximation`
proves

`|f(x)-evaluate(decodedJet,(x-a)/mu)| <= H rho^(k+alpha)/k! + J tau/2`.

The final theorem assumes neither matrix compatibility nor coefficient
accuracy nor a desired transport residual: these are derived. Coefficients,
packets and anchors are independent of the query. Regularity is global ContDiff
and the highest-derivative Holder bound is global; lower tensor bounds are only
required at the finite anchors. The new proof realizes the general decoder
through ordered words. It does not identify the earlier grouped-coordinate
matrix with the new matrix. Closed-cube extension and geometric specialization,
safe-phase aggregation, multiplication approximation, and dense ReLU/quantized
network resource realization remain open. Exact real polynomial multiplication
is used in this analytic decoded approximation theorem.

## Verification

* New roots: 34; frozen source compiled and native LeanChecker replay accepted.
* OxiLean: {A['verdicts']['verified']} verified; 0 unsupported; 0 rejected.
* Native/export: {A['constants_compared']} constants matched, including types,
  values and universe parameters. Normalization only erases metadata and the
  let optimization flag; Lean alpha equivalence is used for expressions.
* Closed, unambiguous dependency graph with no unsafe declarations/admissions.
* Per-root native/export axiom sets agree and use only propext, Quot.sound and
  Classical.choice.
* 18 acceptance tamper controls and 7 structural auditor controls passed.
* All earlier accepted proof source hashes, including SharpTransport and Hodge,
  remain unchanged. Main Lean 4.35 work is preserved; new checks use 4.32.0-rc1.

Mathlib remains at 360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56, with the existing
cached artifacts validated before and after replay. No software or additional
mathlib modules were installed. Windows-mount startup stalls are excluded from
successful checks. Frozen proof input, runtime artifacts and existing pinned
executables use byte-identical Linux-local copies, checked against their source
hashes. The source mirror receipt ties the compiled input to the repository
proof bytes. Native checking uses the unmodified pinned
LeanChecker.replayFromImports API. A full source rebuild of mathlib is not claimed.

Export SHA-256: `{A['export_sha256']}`.

## Reproduction in the preserved workspace

Recreate the earlier pinned runtime/mathlib mirrors if WSL has restarted. Run
`prepare_matrix_replay.py` on Windows; it freezes the proof, records the prior
accepted module and creates Linux-local runners and executable copies. Validate
the original mathlib tree into `replay432/Matrix/mathlib_before.json`. In WSL run
`bash /dev/shm/oxilean-sharp432-20261117/run_matrix432.sh`. Validate mathlib again
into `mathlib_after.json`, then run `promote_matrix_results.py`,
`accept_matrix432.py` and `test_matrix_acceptance.py` on Windows. Pinned workspace
dependencies and the preceding accepted SharpTransport olean are required;
binaries and oleans are not in the delivery bundle.
'''
for directory in [O,M,C]:(directory/'MATRIX_TRANSPORT_REPORT.md').write_text(report,encoding='utf-8',newline='\n')
v=json.loads((O/'FINAL_VALIDATION.json').read_text(encoding='utf-8'));v['formal_theorems']=total
v['full_theorem_scope']='General ordered tensor-word matrix compatibility, sharp normalized transport residuals, bounded correction alphabets, and decoded higher-order Taylor approximation proved with no matrix, residual or coefficient-accuracy premise. Grouped coordinates, domain/geometry and dense quantized ReLU resource realization remain separate.'
v['matrix_transport_continuation']=dict(summary,date='2026-11-17',report='MATRIX_TRANSPORT_REPORT.md')
v['executed_commands'] += [{'name':n,'command':['C:/Python312/python.exe',str(W/f)],'exit_code':0} for n,f in [('matrix_acceptance','accept_matrix432.py'),('matrix_controls','test_matrix_acceptance.py')]]
for directory in [O,M,C]:(directory/'FINAL_VALIDATION.json').write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
note=f'''\n## General ordered matrix continuation, 2026-11-17\n\n34 new verified roots bring the research total to {total}. The concrete tensor-word
matrix is proved compatible with normalized analytic jets in every dimension and
degree. The resulting decoded approximation theorem has no compatibility,
residual or coefficient-accuracy premise. It uses J=sum_(r=0)^k d^r registers;
the earlier grouped-coordinate layout is separate. See
[MATRIX_TRANSPORT_REPORT.md](MATRIX_TRANSPORT_REPORT.md) for the theorem and
remaining domain/geometry and dense-network resource obligations.
'''
for p in [M/'README.md',C/'LEAN_FORMALIZATION_STATUS.md']:
 t=p.read_text(encoding='utf-8');assert '## General ordered matrix continuation, 2026-11-17' not in t
 p.write_text(t.rstrip()+'\n'+note,encoding='utf-8',newline='\n')
print(json.dumps({'new_roots':34,'research_roots_total':total,'export_sha256':A['export_sha256']}))
