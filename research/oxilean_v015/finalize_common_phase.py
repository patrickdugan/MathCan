from pathlib import Path
import hashlib,json,re,shutil
W=Path(__file__).resolve().parent;R=W/'replay432/Common';N=W/'replay435/Common'
A=json.loads((R/'ACCEPTANCE.json').read_text(encoding='utf-8'))
assert A['status']=='accepted' and len(A['theorems'])==23
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,h in A['source_sha256'].items():assert sha(W/'MathCan'/rel)==h
modules=['CommonGateBound','CommonGateCapture']
receipt={'status':'passed','native_and_leanchecker_432':'both modules accepted',
 'native_and_leanchecker_435':'both modules accepted','source_sha256':A['source_sha256'],
 'preserved_435_binary_hashes':(N/'preserved_binary_hashes.txt').read_text(encoding='utf-8'),
 'olean_sha256_432':{m:sha(R/'lib/MathCan'/f'{m}.olean') for m in modules},
 'olean_sha256_435':{m:sha(N/'lib/MathCan'/f'{m}.olean') for m in modules},
 'exporter_sha256':sha(W/'replay432/lean4export-source/.lake/build/bin/lean4export'),
 'oxilean_sha256':sha(W/'build/oxilean-verify')}
(R/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
M=W/'MathCan/research/oxilean_v015';target=M/'pinned432_common';target.mkdir(parents=True,exist_ok=True)
for p in R.iterdir():
 if p.is_file() and p.suffix in {'.json','.log','.lean','.txt','.ndjson','.sha256'}:shutil.copyfile(p,target/p.name)
compat=target/'compat435';compat.mkdir(exist_ok=True)
for p in N.iterdir():
 if p.is_file():shutil.copyfile(p,compat/p.name)
for name in ['check_common432.sh','check_common435.sh','run_common_replay432.sh',
 'prepare_common_replay.py','accept_common432.py','test_common_acceptance.py','finalize_common_phase.py']:
 shutil.copyfile(W/name,M/name)
report=f'''# Common Taylor gate bound and decoded spatial capture

2026-11-16. There are 23 new replayed theorem roots, bringing the research total
to 181 before the separate analytic continuation. The unchanged Hodge root is separate.

`CommonGateBound` proves the uniform constant

    A_D = 2^(k+1) D^k,   D >= 1.

An injective index layout with each coordinate degree at most k has at most one
compatible Taylor entry at each axis degree. The proof filters incompatible and
below-diagonal entries, bounds each remaining power by D^k, and applies the
hockey-stick identity and the bound on binomial coefficients. It does not assume
a matrix norm. The previous unfiltered `rowBudget` is deliberately not bounded
by this constant: its incompatible entries must first be removed.

For |v_gamma| <= C and |h| <= D, every concrete transport coordinate is bounded
by C*A_D. With C=2, all amplitude candidates use the common gate constant 2*A_D.
It does not depend on the streamed site count or the coordinate being updated.

`CommonGateCapture` uses this same constant in the actual Hamming-gated update.
Its frame, exact scheduled stream, robust sentinel stream, and exact/robust spatial
capture theorems reproduce the already-defined concrete clipped reference recurrence.
The frame width remains p+a*J with D<2^p. Layout injectivity and coordinate-degree
bounds are explicit hypotheses, rather than assumed norm bounds.

Validation: Lean 4.32.0-rc1 and preserved Lean 4.35 compilation and leanchecker
both pass. OxiLean verifies {A['verdicts']['verified']} declarations, with zero unsupported
or rejected. All {A['constants_compared']} exported constants match native types,
values and universe parameters. Every root has the same native/exported axiom
inventory, contained in propext, Quot.sound and Classical.choice. All eight
acceptance tamper controls pass. All sources from the preceding four research
corpora are checked against their accepted hashes.

Export SHA-256: `{A['export_sha256']}`.

Copy the included helper scripts into CAMPAIGN_WORK and run
`run_common_replay432.sh`, `check_common435.sh`, and `test_common_acceptance.py`.
See `pinned432_common/ACCEPTANCE.json` and `BUILD_RECEIPT.json` for exact evidence.

This stage proves uniform gate bounds and exact scalar circuit semantics.
The full multivariate smooth approximation and dense network resource theorems
remain open at this checkpoint.
'''
for dest in [M/'COMMON_GATE_BOUND_REPORT.md',W/'Compactification-Theory/research/quantization/COMMON_GATE_BOUND_REPORT.md',W.parent/'outputs/COMMON_GATE_BOUND_REPORT.md']:
 dest.write_text(report,encoding='utf-8',newline='\n')
for path in [M/'README.md',W/'Compactification-Theory/research/quantization/LEAN_FORMALIZATION_STATUS.md']:
 text=path.read_text(encoding='utf-8');intro='Common gate continuation (2026-11-16): 23 new replayed roots establish the\nuniform 2^(k+1)*D^k transport bound and its exact/robust decoded spatial capture.\nRead COMMON_GATE_BOUND_REPORT.md. This checkpoint has 181 research roots.\n\n'
 path.write_text(intro+text,encoding='utf-8',newline='\n')
print('Common-bound proof phase and evidence prepared for commit.')
