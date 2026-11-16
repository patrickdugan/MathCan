from pathlib import Path
import gzip
import hashlib
import json
import shutil
from datetime import datetime, timezone

W = Path(__file__).resolve().parent
O = W.parent/'outputs'
M = W/'MathCan/research/oxilean_v015'
C = W/'Compactification-Theory/research/quantization'
R = W/'replay432/Synthesis'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins = {
    'toolchains/lean-4.32.0-rc1-linux/bin/lean': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    'toolchains/lean-4.32.0-rc1-linux/bin/leanchecker': 'c7c51e296d28dd443ed60f9414feef41253ede89dea76dbb2adde29768c3ed5f',
    'toolchains/lean-4.32.0-rc1-linux/lib/lean/LeanChecker.olean': '7ba4f458fef64a5c75f2eef1760d2c21690bd8a41210d298330c7554cf2e5c50',
    'replay432/lean4export-source/.lake/build/bin/lean4export': 'e6580597a1482740114b5a1a05add574334a5eeaed5f4f5c9cd670e146859009',
    'build/oxilean-verify': '831e7ad751d69d7f27e8ee59ec40246a6256e971e11f418b0e92f9722771e9fa',
    'MathCan/MathCan/Hodge.lean': '6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5',
}
for rel, digest in pins.items():
    assert sha(W/rel) == digest, rel
A = json.loads((R/'ACCEPTANCE.json').read_text(encoding='utf-8'))
manifest = json.loads((R/'manifest.json').read_text(encoding='utf-8'))
assert A['status'] == 'accepted' and len(A['theorems']) == 47
assert set(row['name'] for row in A['theorems']) == set(manifest['theorems'])
assert A['vendor_roots'] == []
assert A['verdicts']['unsupported'] == A['verdicts']['rejected'] == 0
assert sha(R/'Lemmas.ndjson') == A['export_sha256']
for rel, digest in A['source_sha256'].items():
    assert sha(W/'MathCan'/rel) == digest
for phase in ['before', 'after']:
    assert json.loads((R/f'mathlib_{phase}.json').read_text(encoding='utf-8'))['status'] == 'matched'
controls = (R/'acceptance_controls.log').read_text(encoding='utf-8')
assert 'Ran 12 tests' in controls and controls.rstrip().endswith('OK')
audit_controls = (R/'auditor_controls.log').read_text(encoding='utf-8')
assert 'Ran 7 tests' in audit_controls and audit_controls.rstrip().endswith('OK')
receipt = {
    'status': 'passed', 'lean': '4.32.0-rc1', 'new_authored_roots': 47,
    'mathlib_revision': A['mathlib_revision'], 'source_sha256': A['source_sha256'],
    'native_kernel_method': A['native_kernel_method'],
    'binary_sha256': {rel: digest for rel, digest in pins.items() if rel != 'MathCan/MathCan/Hodge.lean'},
    'olean_sha256': {name.rsplit('.',1)[-1]+'.olean':
        sha(R/'lib/ApproximationMathlib'/(name.rsplit('.',1)[-1]+'.olean'))
        for name in manifest['modules']},
    'mathlib_receipts': {name: sha(W/name) for name in [
        'MATHLIB_SOURCE_RECEIPT.json', 'MATHLIB_PACKAGE_RECEIPT.json', 'MATHLIB_ARTIFACT_RECEIPT.json']},
    'previous_sources': 'All prior accepted proof source hashes rechecked by acceptance validator',
    'structural_auditor_sha256': sha(W/'audit_export_fast.py'),
    'runtime_mirror_receipts_sha256': {name:sha(R/name) for name in [
        'mathlib_mirror.json','mathlib_mirror_after.json','mirror_used.json',
        'mathlib_mirror_after_native.json']},
}
(R/'BUILD_RECEIPT.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8', newline='\n')
summary = {key: A[key] for key in ['status', 'export_sha256', 'verdicts', 'constants_compared',
    'source_sha256', 'mathlib_revision', 'native_kernel_method', 'standard_axioms']}
summary.update(new_authored_roots=47, research_roots_total=257,
               acceptance_tamper_controls=12,
               structural_auditor_controls=7,
               roots=[row['name'] for row in A['theorems']])
(R/'VERIFICATION_SUMMARY.json').write_text(json.dumps(summary, indent=2)+'\n', encoding='utf-8', newline='\n')
target = M/'pinned432_synthesis'
target.mkdir(parents=True, exist_ok=True)
for p in R.iterdir():
    if not p.is_file() or p.suffix not in {'.json', '.log', '.lean', '.txt', '.sha256', '.ndjson', '.exitcode'}:
        continue
    if p.suffix == '.ndjson':
        dest = target/(p.name+'.gz')
        with p.open('rb') as src, dest.open('wb') as raw:
            with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as out:
                shutil.copyfileobj(src, out)
        with gzip.open(dest, 'rb') as src:
            assert hashlib.file_digest(src, 'sha256').hexdigest() == A['export_sha256']
    else:
        shutil.copyfile(p, target/p.name)
helpers = ['synthesis_env432.sh', 'freeze_synthesis432.sh', 'build_synthesis432.sh',
    'kernel_synthesis432.sh', 'export_synthesis432.sh', 'compare_synthesis432.sh',
    'prepare_synthesis_replay.py', 'accept_synthesis432.py', 'test_synthesis_acceptance.py',
    'check_synthesis_source.py', 'finalize_synthesis_phase.py',
    'record_push_receipt.py', 'package_synthesis_results.py', 'check_synthesis_git_content.py',
    'fast_synthesis_replay432.sh', 'promote_fast_synthesis432.py',
    'mirror_synthesis_mathlib432.py', 'stop_slow_synthesis_export.py', 'probe_stock_synthesis432.sh']
helpers += ['finish_fast_synthesis432.sh', 'audit_export_fast.py',
            'test_audit_export_fast.py', 'prepare_fast_auditor.py', 'check_mirror_native432.py']
for name in helpers:
    shutil.copyfile(W/name, M/name)
for name in ['ACCEPTANCE.json', 'BUILD_RECEIPT.json', 'VERIFICATION_SUMMARY.json']:
    shutil.copyfile(R/name, O/('SYNTHESIS_'+name))
for name in ['BUILD_RECEIPT.json', 'VERIFICATION_SUMMARY.json']:
    shutil.copyfile(R/name, C/('MULTIVARIATE_SYNTHESIS_'+name))
report = f'''# Multivariate Taylor synthesis and constructed coefficient accuracy

This stage adds **47 authored theorem roots**, bringing the research campaign
to **257 roots**, including the earlier 12 attributed upstream Taylor roots.
The unchanged Hodge theorem remains separate. All 47 new roots compile from
frozen sources and pass native Lean kernel replay and independent OxiLean replay.

## Mathematical result

`MultivariateTaylor` constructs coefficients from Frechet derivative tensors at
a fixed anchor. Multilinear expansion over coordinate words and grouping by
multiindex prove that evaluating these query-independent coefficients gives
the actual multivariate Taylor polynomial. Dimension and degree are arbitrary.
The canonical rectangular index set has `(k+1)^d` elements, and the coefficient
of a multiindex with total degree above k is zero by its defining finite sum.

`MultivariateBounds` bounds those coefficients using operator norms, proves
coefficient perturbation estimates and derives the degree-n integer remainder.
`MultivariateHolder` derives the degree-k fractional remainder, for k>=1 and
alpha>=0, from a Holder estimate on the highest derivative tensor. Regularity
is actual global ContDiff on R^d; segment derivative bounds are explicit.

`JetSynthesis` and `FrameSynthesis` construct integer corrections, finite frames
and clipped reference states using the existing concrete Taylor transport
predictor. Rounding contributes at most tau/2. Clipping is nonexpansive toward
targets in [-C,C]. Consequently every reference state is within tau/2 of its
target, independently of stream length. The initial state is constructed by
the same rounding and clipping operation.

`SynthesisCapture` connects valid synthesized frames to the existing base-4
sentinel decoder, Hamming selector, common gate bound and decoded spatial
capture. `MultivariateCapture.jet_accuracy` instantiates its targets with the
derivative-tensor coefficients at the anchor sites. **The coefficient-accuracy
contract is proved, rather than assumed, in the final approximation theorems.**

For the selected anchor a and ||x-a||<=rho<=1, the actual decoded coefficient
vector q therefore satisfies:

* degree n, bounded derivative of order n+1:
  `|f(x)-evaluate(q,x-a)| <= M*rho^(n+1)/(n+1)! + (n+1)^d*tau/2`;
* degree k>=1, Holder exponent alpha>=0 on derivative k:
  `|f(x)-evaluate(q,x-a)| <= H*rho^(k+alpha)/k! + (k+1)^d*tau/2`.

Only the selected anchor must be close to the query. The coefficients, frames
and reference trajectory do not depend on that query. Valid sites, schedule
length, bounded step metadata, anchor derivative bounds and finite bit-width
inequalities remain explicit hypotheses.

The correction alphabet uses the proved general predictor bound:
`N >= (C+C*A_D)/tau+1/2`, `D<2^p`, `2*N<2^a`, with
`A_D=2^(k+1)*D^k` and `C=(sum_{{j=0}}^k d^j)*M`. A separate lemma proves that
finite parameters satisfying these inequalities exist. This bound grows as tau
decreases; it does not give the sharper small alphabet needed for the target
network parameter rate. The corresponding sharp transport residual estimate,
closed-cube/domain and geometric specialization, and dense ReLU arithmetic and
resource realization remain open. Polynomial evaluation uses exact real
multiplication. This stage does not finish the full quantized network theorem.

## Verification

| Check | Result |
|---|---|
| New authored theorem roots | 47 |
| Frozen-source Lean compilation | All seven modules passed |
| Native kernel replay | All seven modules passed |
| OxiLean dependency declarations | {A['verdicts']['verified']} verified |
| Unsupported / rejected declarations | 0 / 0 |
| Native constants compared with export | {A['constants_compared']} matched |
| Acceptance tamper controls | 12 passed |
| Structural auditor control/equivalence tests | 7 passed |

Every exported dependency receives a checked per-declaration verdict. The export
graph is closed, has unambiguous names, and contains no unsafe declarations.
Every exported type, proof/definition value and universe-parameter list matches
the native environment; normalization only removes metadata and normalizes the
nondependent-let optimization flag.
Expression equality uses Lean's alpha equivalence for binder names/annotations.
Native and exported axiom inventories agree for each of the 47 roots and contain
only propext, Quot.sound and Classical.choice.
There are no admitted proofs or added mathematical axioms in the new modules.

Native checking calls the unmodified pinned LeanChecker.replayFromImports API
from its pinned module, omitting the stock CLI recursive search-path discovery.
DirectKernel.lean and direct_kernel.log record every module. The IO harness is
not part of the exported mathematical declarations. No Lean 4.35 replay is
claimed for these Mathlib modules; the main MathCan 4.35 toolchain is preserved.
All previously accepted proof source hashes and Hodge source bytes remain intact.

Mathlib stays at 360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56 (v4.32.0-rc1).
The 1,906 Mathlib/helper source files, eight pinned packages and 2,145 cached
artifact modules (19,305 retained artifacts) are validated before the frozen
rebuild and again for final acceptance after native replay. Official cached artifacts
are used; a full source rebuild of Mathlib
is not claimed. The dependency-closed exported proof terms are independently
checked. No extra Mathlib modules or software installs were required this stage.
The final export/source comparison uses a Linux-local copy of 8,580 runtime
artifacts (1,582,920,792 bytes), checked against the same pinned artifact receipt.
Source/copy hashes agree and every mirror file is rechecked around the replay.

Export SHA-256: `{A['export_sha256']}`.
The BUILD_RECEIPT and acceptance files record source, artifact and binary hashes.
Startup failures before the frozen rebuild are infrastructure failures and are
not included as successful checks. Earlier pending checkpoints are historical.
The additional stock CLI path-discovery probe timed out (exit 124) and is not
counted. The accepted native result is the completed seven-module direct API
replay. A slow Windows-mounted export was interrupted and excluded; the complete
Linux-local replacement was checked and copied back with byte/hash equality.
The structural auditor's missing-name query was changed from repeated table
scans to direct dictionary membership. The original auditor remains intact;
all existing fixtures produce exactly equal results with the optimized version,
including target-scoped closure. The new graph is computed by audit_export_fast.py.

## Reproduction

Use the existing pinned campaign workspace. Restore the helper scripts into
CAMPAIGN_WORK and provision the previously verified analytic/core libraries and
recorded Mathlib artifacts. Run mirror_synthesis_mathlib432.py and set
SYNTHESIS_MATHLIB_MIRROR to the target recorded in mathlib_mirror.json before
using the replay helpers. Run the source admission scan and Mathlib validator,
then freeze_synthesis432.sh and build_synthesis432.sh. After the build finishes,
kernel_synthesis432.sh and export_synthesis432.sh may run concurrently: they read
the frozen artifacts and write separate logs. Run compare_synthesis432.sh after
the export/OxiLean stage. Once every replay and comparison has passed, validate
Mathlib again, recheck the mirror with mirror_synthesis_mathlib432.py --verify-only,
run accept_synthesis432.py and test_synthesis_acceptance.py, and
retain all logs. Publication requires every stage to finish successfully.
For slow Windows-mounted I/O, fast_synthesis_replay432.sh writes the export,
OxiLean results and source comparison to RAM-backed Linux temporary storage.
finish_fast_synthesis432.sh can resume the audit and source comparison in
parallel after a complete, per-declaration-verified export already exists.
After all checks finish, promote_fast_synthesis432.py verifies and bulk-copies
those results into the canonical evidence directory. The optional runtime cache
helper copies only recorded artifacts, checks source/copy SHA-256 equality and
uses available-memory and filesystem-capacity guards; it downloads nothing.
The accepted raw export is stored as deterministic gzip in pinned432_synthesis;
decompress it into replay432/Synthesis/Lemmas.ndjson to rerun offline acceptance.
The preceding CompareLemmas.lean supplies the independent parser comparison
template used by prepare_synthesis_replay.py. Runtime binaries and oleans are
not committed or bundled.

These invariants can inform register bounds and correction-accuracy objectives
for looped-layer transformer experiments. The Lean results establish properties
of the specified mathematical decoder and evaluator; no new empirical claim
about trained transformer implementations is made here. No external message or
repository comment was sent in this continuation.
'''
for dest in [M/'MULTIVARIATE_SYNTHESIS_REPORT.md', C/'MULTIVARIATE_SYNTHESIS_REPORT.md',
             O/'MULTIVARIATE_SYNTHESIS_REPORT.md']:
    dest.write_text(report, encoding='utf-8', newline='\n')
intro = '''Multivariate synthesis continuation: 47 new authored roots prove arbitrary-dimensional
Taylor jet synthesis, constructed tau/2 coefficient accuracy and decoded smooth/Holder
approximation. All 257 research roots now have replay evidence. See
MULTIVARIATE_SYNTHESIS_REPORT.md for verification and remaining network obligations.

'''
for dest in [M/'README.md', C/'LEAN_FORMALIZATION_STATUS.md']:
    text = dest.read_text(encoding='utf-8')
    if not text.startswith(intro):
        dest.write_text(intro+text, encoding='utf-8', newline='\n')
project_readme = W/'MathCan/research/approximation_mathlib432/README.md'
text = project_readme.read_text(encoding='utf-8')
start = text.index('Coefficient accuracy of the concrete reference recurrence is an explicit') if (
    'Coefficient accuracy of the concrete reference recurrence is an explicit' in text
) else text.index('The multivariate continuation constructs')
end = text.index('The standard Lake project', start)
text = text[:start]+'''The multivariate continuation constructs fixed-anchor coefficients directly from
Frechet derivative tensors (`MultivariateTaylor`), proves their norm and
perturbation bounds (`MultivariateBounds`) and integer/Holder remainders
(`MultivariateBounds`, `MultivariateHolder`). `JetSynthesis` and `FrameSynthesis`
construct rounded/clipped correction frames and prove uniform tau/2 accuracy.
`SynthesisCapture` connects these frames to the existing decoded spatial capture.
`MultivariateCapture` proves the resulting coefficient accuracy and the final
smooth/Holder approximation bounds without an assumed accuracy contract.

These results cover arbitrary dimension and degree with global ContDiff
regularity, segment derivative estimates, and explicit site/schedule and bit
width premises. The correction alphabet is finite but uses a general O(1/tau)
predictor bound. The sharp small-alphabet transport estimate, closed-cube/domain
and geometric specialization, and dense ReLU arithmetic/resource compiler remain
open. Exact polynomial evaluation is not yet realized as the desired bounded,
quantized ReLU network. See ../oxilean_v015/MULTIVARIATE_SYNTHESIS_REPORT.md.

'''+text[end:]
project_readme.write_text(text, encoding='utf-8', newline='\n')
old = json.loads((O/'FINAL_VALIDATION.json').read_text(encoding='utf-8'))
old['formal_theorems'] = 257
old['native_coverage'] = {'4.32.0-rc1': 'all 257 research roots',
    'preserved 4.35.0': '181 core roots; excludes isolated Mathlib analysis and synthesis'}
old['multivariate_synthesis_continuation'] = summary
old['full_theorem_scope'] = ('Query-independent multivariate Taylor jets, constructed correction frames and '
    'coefficient accuracy, decoded spatial capture, and smooth/Holder polynomial approximation proved. '
    'Sharp small-alphabet transport bounds, domain/geometry specialization and dense ReLU '
    'arithmetic/resource realization remain open.')
for dest in [O/'FINAL_VALIDATION.json', M/'FINAL_VALIDATION.json', C/'FINAL_VALIDATION.json']:
    dest.write_text(json.dumps(old, indent=2)+'\n', encoding='utf-8', newline='\n')
(O/'README.md').write_text('''# Multivariate synthesis and coefficient accuracy

Read MULTIVARIATE_SYNTHESIS_REPORT.md and SYNTHESIS_VERIFICATION_SUMMARY.json.
This phase adds 47 authored roots, reaching 257 verified research roots; the
unchanged Hodge theorem is separate. The full quantized ReLU resource theorem
remains open. Earlier pending checkpoints describe the prior runtime failure.
PUSH_RECEIPT.json records the latest verified remote heads after publication.
''', encoding='utf-8', newline='\n')
runtime_path = O/'RUNTIME_RECOVERY_STATUS.json'
if runtime_path.exists():
    runtime = json.loads(runtime_path.read_text(encoding='utf-8-sig'))
    runtime.update(status='recovered_verification_passed',
        checked_at_utc=datetime.now(timezone.utc).isoformat(),
        new_oxilean_verified_roots=47, push_status='Verified work ready to commit and push',
        required_action='None')
    runtime_path.write_text(json.dumps(runtime, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps({'status': 'prepared_verified_phase', 'new_roots': 47,
                  'research_roots': 257, 'verdicts': A['verdicts']}, indent=2))
