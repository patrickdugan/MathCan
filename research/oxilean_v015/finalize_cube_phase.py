from pathlib import Path
import gzip,hashlib,json,shutil
W=Path(__file__).resolve().parent;R=W/'replay432/Cube';O=W.parent/'outputs'
M=W/'MathCan/research/oxilean_v015';C=W/'Compactification-Theory/research/quantization'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
A=json.loads((R/'ACCEPTANCE.json').read_text(encoding='utf-8'));manifest=json.loads((R/'manifest.json').read_text(encoding='utf-8'))
assert A['status']=='accepted' and len(A['theorems'])==58 and A['verdicts']['unsupported']==A['verdicts']['rejected']==0
assert sha(R/'Lemmas.ndjson')==A['export_sha256']
for name,count in [('acceptance_controls.log',19),('auditor_controls.log',7)]:
 t=(R/name).read_text(encoding='utf-8');assert f'Ran {count} tests' in t and t.rstrip().endswith('OK')
for rel,digest in A['source_sha256'].items():assert sha(W/'MathCan'/rel)==digest
assert sha(W/'MathCan/MathCan/Hodge.lean')=='6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5'
pins={}
for line in (R/'binary_before.sha256').read_text(encoding='utf-8').splitlines():
 digest,path=line.split('  ',1);p=W/path.split('/work/',1)[1];assert sha(p)==digest;pins[p.relative_to(W).as_posix()]=digest
total=json.loads((W/'replay432/Matrix/VERIFICATION_SUMMARY.json').read_text(encoding='utf-8'))['research_roots_total']+58
scope='Intrinsic closed-cube Taylor jets, exact clipped-anchor serpentine schedule, bounded motion tags and decoded spatial approximation. The selected-anchor distance is derived; the grid-scale coefficient error has its required D^k factor. Safe-phase aggregation and dense ReLU resource realization remain separate.'
receipt={'status':'passed','lean':'4.32.0-rc1','new_authored_roots':58,'research_roots_total':total,
 'source_sha256':A['source_sha256'],'binary_sha256':pins,'mathlib_revision':A['mathlib_revision'],
 'native_kernel_method':A['native_kernel_method'],'source_mirror_sha256':sha(R/'source_mirror.json'),
 'olean_sha256':{'ApproximationMathlib.CubeApproximation':sha(R/'lib/ApproximationMathlib/CubeApproximation.olean')},
 'mirror_receipts_sha256':{p.name:sha(p) for p in R.glob('*mirror*.json')},'scope':scope}
(R/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
summary={k:A[k] for k in ['status','export_sha256','verdicts','constants_compared','source_sha256','mathlib_revision','native_kernel_method','standard_axioms']}
summary.update(new_authored_roots=58,research_roots_total=total,acceptance_tamper_controls=19,structural_auditor_controls=7,roots=manifest['theorems'])
(R/'VERIFICATION_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8',newline='\n')
target=M/'pinned432_cube';target.mkdir(parents=True,exist_ok=True)
for p in R.iterdir():
 if not p.is_file() or p.name.startswith('lsp_') or p.suffix not in ['.json','.log','.lean','.txt','.sha256','.ndjson']:continue
 if p.suffix=='.ndjson':
  dest=target/(p.name+'.gz')
  with p.open('rb') as src,dest.open('wb') as raw:
   with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as out:shutil.copyfileobj(src,out)
  with gzip.open(dest,'rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==A['export_sha256']
 else:shutil.copyfile(p,target/p.name)
helpers=['prepare_cube_replay.py','check_cube_spatial_source.py','cube_env432.sh','run_cube432.sh','check_cube_mirrors.py','accept_cube432.py',
 'test_cube_acceptance.py','promote_cube_results.py','finalize_cube_phase.py','check_cube_git_content.py',
 'record_cube_push_receipt.py','package_cube_results.py']
for name in helpers:shutil.copyfile(W/name,M/name)
for name in ['ACCEPTANCE.json','BUILD_RECEIPT.json','VERIFICATION_SUMMARY.json']:shutil.copyfile(R/name,O/('CUBE_'+name))
for name in ['BUILD_RECEIPT.json','VERIFICATION_SUMMARY.json']:shutil.copyfile(R/name,C/('CUBE_'+name))
report=f'''# Intrinsic closed-cube regularity and spatial anchor coverage

58 authored roots pass frozen Lean compilation, native kernel replay and OxiLean.
The campaign now has {total} research roots, including the earlier 12 attributed
upstream Taylor roots. Hodge and all previously accepted proof sources are unchanged.

## Closed-cube regularity

`CubeTaylor.cube d` is the coordinate cube [0,1]^d in the supremum norm.
`cube_convex`, `cube_uniqueDiff`, and `cube_segment` prove convexity, unique
differentiability and containment of every interpolation segment, including faces
and corners. The new derivative tensors are `iteratedFDerivWithin` on this cube.
No values or regularity of f outside the cube are required.

`dir_smooth`, `dir_tensor`, `dir_ofFn` and `line_derivatives` identify recursively
defined within-directional derivatives with genuine within-Frechet tensors and
with scalar derivatives on the closed Taylor interval. `holder_remainder` derives
the multivariate Holder Taylor estimate from intrinsic C^k regularity and a Holder
bound on the original highest within-derivative tensor. Boundary points are
handled by within-interval derivatives; a global smooth extension is not constructed
or assumed.

`values` uses the preceding ordered-word register layout, J=sum_(r=0)^k d^r,
with z_w(a)=mu^r/r! D^r_cube f(a)[e_w]. `row_compatibility` proves that the same
integer motion matrix represents its genuine Taylor polynomial. `axes_difference`,
`axis_line_holder`, `axis_remainder`, and `matrix_residual` derive the common
normalized residual from the highest within-tensor Holder bound. The top rank,
degree-zero transport, zero motion and clipped repeated boundary anchors are covered.

## Concrete spatial anchors and motion stream

`CubeAnchors.unrank` is an explicit inverse of the existing scalar serpentine rank;
`unrank_rank` proves the inverse on every valid grid digit vector. `unrank_bound`
and `CubeWalk.unrank_step` prove bounded digits and unit-coordinate adjacency.

For integer cap, D>=1, integer shifts t_j, coarse block c, and mu*cap=1, the
physical grid anchors are

`a(g)_j = mu * clamp_[0,cap](D*(c_j*K+g_j)+t_j-D)`.

`point_in_cube` keeps every anchor in [0,1]^d. `point_anchor` identifies this
integer lattice formula with the clipped real anchor

`clip_[0,1](h*(c_j*K+g_j+theta_j-1)), h=mu*D, theta_j=t_j/D`.

`lattice_step` and `adjacent_motion` prove that adjacent anchors differ by
`mu*q*e_axis` for a signed integer q with |q|<=D. `delta_motion` represents this
step in the existing finite motion-tag alphabet. `schedule` constructs the tags
for all K^d anchors, and `schedule_anchors` proves that their actual recursive
physical orbit equals the serpentine grid enumeration. Boundary clipping can
shorten a step to zero; these steps remain valid tags. The tags, anchor orbit,
true jets and correction packets depend on the coarse block and fixed parameters,
and are independent of the query's fine address.

For a query x in the cube whose phase coordinates satisfy the explicit safe-cell
inequalities, `safe_coverage` proves ||x-a||<=h. `selected_coverage` and
`schedule_selected` identify that anchor with the one selected by the existing
spatial rank circuit. No assumed selected-anchor distance, schedule alignment,
unit-step oracle or cube-membership condition remains in `CubeSpatial.approximation`.

## Connection to decoded approximation

`CubeCapture.targets_residuals` discharges the actual within-jet transport residuals.
The preceding Hamming selector, signed correction quantizer, base-4 sentinel
decoder and clipped reference recurrence prove tau/2 coefficient accuracy. The
finite correction alphabet retains the common bound

`N >= 2 H D^(k+alpha) + A_D/2 + 1/2`, `A_D=2^(k+1) D^k`.

The tag and correction bit widths satisfy `tagCount(d,D)<2^p` and `2N<2^a`.
With k=n+1>=1, intrinsic C^k cube regularity, highest-tensor Holder constant H,
alpha>=0, derivative-tensor bound M on the cube, mu>0, tau>0,
`mu^(k+alpha)<=2 tau`, and the stated safe-cell and finite-parameter inequalities,
`CubeSpatial.approximation` proves for the actual decoded and spatially captured jet

`|f(x)-evaluate(decodedJet,(x-a)/mu)| <= H*(D*mu)^(k+alpha)/k! + J*D^k*tau/2`.

The factor D^k is necessary in this interface: geometric coverage is h=D*mu,
so normalized query coordinates have norm at most D. The older global-regularity
theorem assumed distance rho<=mu and obtained J*tau/2; its source is preserved.
The new `evaluation_error` supplies the correct coefficient sensitivity at radius D.

The closed-cube theorem assumes neither a global extension nor matrix compatibility,
transport residuals, coefficient accuracy, nor anchor coverage. It proves these
from regularity and the concrete finite construction. It remains a safe-phase
analytic decoded-polynomial theorem. Coverage by enough safe phases and median
aggregation, approximate multiplication, and dense quantized ReLU network resource
realization remain open. Exact real polynomial multiplication is used. The older
grouped-multiindex layout is separate from the ordered-word realization.

## Verification

* New roots: 58; frozen source compiled and native LeanChecker replay accepted.
* OxiLean: {A['verdicts']['verified']} verified; 0 unsupported; 0 rejected.
* Native/export: {A['constants_compared']} constants matched in type, value and
  universe parameters. Comparison erases only metadata and the let optimization
  flag; expression alpha equivalence is retained.
* Closed, unambiguous dependency graph; no unsafe declarations or admissions.
* Per-root native/export axiom sets agree and use only propext, Quot.sound and
  Classical.choice.
* 19 acceptance tamper controls and 7 structural auditor controls passed.
* All prior accepted source hashes, including WordTransport, SharpTransport,
  the original spatial interface, and Hodge, remain unchanged.
* The newly imported original SpatialInterface artifact was also rebuilt from
  its unchanged source; the complete olean is byte-identical to the cached artifact.

Lean is pinned at 4.32.0-rc1 (b4812ae53eea93439ad5dce5a5c26591c31cb697).
Mathlib remains at 360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56 with all retained
artifacts validated before and after replay. No new software or mathlib modules
were installed. Native checking uses the unmodified pinned
LeanChecker.replayFromImports API. Runtime, exporter/parser, previous module and
mathlib artifacts are checked byte-for-byte in Linux-local mirrors; a source
mirror receipt binds frozen compiled input to the committed proof bytes. A full
source rebuild of mathlib is not claimed. Main Lean 4.35 work is preserved.

Proof SHA-256: `{next(iter(A['source_sha256'].values()))}`.

Export SHA-256: `{A['export_sha256']}`.

## Reproduction in the preserved workspace

Recreate the earlier pinned runtime/mathlib mirrors if WSL has restarted. Run
`prepare_cube_replay.py` on Windows to freeze the source and mirror the earlier
accepted SharpTransport, WordTransport and SpatialInterface artifacts. Validate
the original mathlib tree into `replay432/Cube/mathlib_before.json`; in WSL run
`bash /dev/shm/oxilean-sharp432-20261117/run_cube432.sh`. Validate mathlib again
into `mathlib_after.json`, then run `promote_cube_results.py`, `accept_cube432.py`
and `test_cube_acceptance.py` on Windows. Native binaries and oleans are local
proof dependencies and are not included in the delivery bundle.
'''
for directory in [O,M,C]:(directory/'CUBE_APPROXIMATION_REPORT.md').write_text(report,encoding='utf-8',newline='\n')
v=json.loads((O/'FINAL_VALIDATION.json').read_text(encoding='utf-8'));v['formal_theorems']=total
v['full_theorem_scope']=scope
v['closed_cube_continuation']=dict(summary,date='2026-11-17',report='CUBE_APPROXIMATION_REPORT.md')
v['executed_commands'] += [{'name':n,'command':['C:/Python312/python.exe',str(W/f)],'exit_code':0} for n,f in [('cube_acceptance','accept_cube432.py'),('cube_controls','test_cube_acceptance.py')]]
for directory in [O,M,C]:(directory/'FINAL_VALIDATION.json').write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
note=f'''\n## Closed-cube and anchor coverage continuation, 2026-11-17\n\n58 new verified roots bring the research total to {total}. Intrinsic closed-cube
regularity now suffices for decoded spatial approximation. Clipped grid anchors,
their bounded motion tags, serpentine schedule and selected-anchor distance are
constructed and proved. The grid-scale coefficient error includes the required
D^k factor. See [CUBE_APPROXIMATION_REPORT.md](CUBE_APPROXIMATION_REPORT.md) for
the precise safe-phase theorem and remaining phase aggregation and network
resource obligations.\n'''
for p in [M/'README.md',C/'LEAN_FORMALIZATION_STATUS.md']:
 t=p.read_text(encoding='utf-8');assert '## Closed-cube and anchor coverage continuation, 2026-11-17' not in t
 latest=f'''Current checkpoint (2026-11-17): intrinsic closed-cube regularity and concrete
anchor coverage are proved for the decoded safe-phase approximation theorem.
58 new verified roots bring the campaign to {total}. See
[CUBE_APPROXIMATION_REPORT.md](CUBE_APPROXIMATION_REPORT.md). Phase aggregation
and dense quantized ReLU resource realization remain open. Earlier checkpoints follow.\n\n'''
 p.write_text(latest+t.rstrip()+'\n'+note,encoding='utf-8',newline='\n')
umbrella=W/'MathCan/research/approximation_mathlib432/ApproximationMathlib.lean'
t=umbrella.read_text();assert 'import ApproximationMathlib.CubeApproximation' not in t
umbrella.write_text(t.rstrip()+'\nimport ApproximationMathlib.CubeApproximation\n',encoding='utf-8',newline='\n')
projectReadme=umbrella.parent/'README.md'
t=projectReadme.read_text(encoding='utf-8')
t=t.replace('# Scalar analytic approximation bridge','# Analytic approximation bridge')
old='''These results cover arbitrary dimension and degree with global ContDiff
regularity, segment derivative estimates, and explicit site/schedule and bit
width premises. The correction alphabet is finite but uses a general O(1/tau)
predictor bound. The sharp small-alphabet transport estimate, closed-cube/domain
and geometric specialization, and dense ReLU arithmetic/resource compiler remain
open. Exact polynomial evaluation is not yet realized as the desired bounded,
quantized ReLU network. See ../oxilean_v015/MULTIVARIATE_SYNTHESIS_REPORT.md.'''
new='''The subsequent `SharpTransport` and `WordTransport` modules prove a uniform
correction alphabet and general ordered-word matrix compatibility. The current
`CubeApproximation` module proves intrinsic closed-cube Taylor regularity,
clipped-anchor serpentine coverage and the actual decoded spatial approximation.
Its 58 new roots bring the verified campaign to 374 research roots. For k>=1
the safe-phase error is H*(D*mu)^(k+alpha)/k! + J*D^k*tau/2. A global smooth
extension, a compatibility oracle and an assumed anchor-distance bound are not
premises. Safe-phase aggregation, approximate multiplication and the dense
quantized ReLU resource compiler remain open. See
[CUBE_APPROXIMATION_REPORT.md](../oxilean_v015/CUBE_APPROXIMATION_REPORT.md).
For the current frozen replay, restore the cube helpers into CAMPAIGN_WORK and
follow that report; the analytic helpers below describe the earlier scalar run.'''
assert old in t
projectReadme.write_text(t.replace(old,new),encoding='utf-8',newline='\n')
print(json.dumps({'new_roots':58,'research_roots_total':total,'export_sha256':A['export_sha256']}))
