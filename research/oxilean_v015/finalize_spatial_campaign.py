from pathlib import Path
import hashlib
import json
import shutil

W = Path(__file__).resolve().parent
O = W.parent/'outputs'
M = W/'MathCan/research/oxilean_v015'
C = W/'Compactification-Theory/research/quantization'
R = W/'replay432/SpatialScalar'
N = W/'replay435/SpatialFormalization'
A = json.loads((R/'ACCEPTANCE.json').read_text(encoding='utf-8'))
manifest = json.loads((R/'manifest.json').read_text(encoding='utf-8'))
assert A['status']=='accepted' and len(A['theorems'])==len(manifest['theorems'])==42
assert A['verdicts']['unsupported']==A['verdicts']['rejected']==0
assert len(list(N.glob('*_leanchecker.log')))==4
for p in N.glob('*.log'):
    assert 'error:' not in p.read_text(encoding='utf-8')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for rel,digest in A['source_sha256'].items():
    assert sha(W/'MathCan'/rel)==digest
receipt = {'status':'passed', 'source_sha256':A['source_sha256'],
    'native_lean':'4.32.0-rc1', 'leanchecker':'4.32.0-rc1',
    'project_compatibility':'all four modules compiled and leanchecker accepted in preserved Lean 4.35.0',
    'preserved_435_binary_hashes':(N/'preserved_binary_hashes.txt').read_text(encoding='utf-8'),
    'exporter_source':'3de59f10bc4b4a0f2de698597aeb1246caa0df0a',
    'oxilean_source':'3adb983d2aefc6a596bdc8b63438f54feecd1f55',
    'olean_sha256_432':{m:sha(R/'lib/MathCan'/f'{m.rsplit(".",1)[-1]}.olean') for m in manifest['modules']},
    'olean_sha256_435':{m:sha(N/'lib/MathCan'/f'{m.rsplit(".",1)[-1]}.olean') for m in manifest['modules']},
    'scope':'spatial scalar semantics and exact bounded streaming capture; analytic theorem and dense compiler correctness remain open'}
(R/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
target = M/'pinned432_spatial'
target.mkdir(parents=True,exist_ok=True)
for p in R.iterdir():
    if p.is_file() and p.suffix in {'.json','.log','.lean','.txt','.ndjson'}:
        shutil.copyfile(p,target/p.name)
compat = target/'compat435'
compat.mkdir(exist_ok=True)
for p in N.iterdir():
    if p.is_file(): shutil.copyfile(p,compat/p.name)
for name in ['formalize_spatial432.sh','replay_spatial_scalar432.sh','prepare_spatial_replay.py',
             'accept_spatial432.py','test_spatial_acceptance.py','check_spatial_new435.sh',
             'validate_spatial_final.py','finalize_spatial_campaign.py','package_results.py']:
    shutil.copyfile(W/name,M/name)
for name in ['new_spatial_acceptance','spatial_acceptance_tamper_controls',
             'retained_hodge_acceptance','retained_14_lemma_acceptance']:
    shutil.copyfile(W/'logs'/f'{name}.log',target/f'{name}.log')
shutil.copyfile(O/'FINAL_VALIDATION.json',M/'FINAL_VALIDATION.json')
shutil.copyfile(R/'ACCEPTANCE.json',O/'SPATIAL_LEMMAS_ACCEPTANCE.json')
for module in manifest['modules']:
    name=module.rsplit('.',1)[-1]+'.lean'
    shutil.copyfile(W/'MathCan/MathCan'/name,O/name)
for name in ['OXILEAN_DECLARATION_VERDICTS.json','OXILEAN_AXIOM_AUDIT.json','PROVENANCE.json']:
    p=O/name
    data=json.loads(p.read_text(encoding='utf-8'))
    if name=='OXILEAN_DECLARATION_VERDICTS.json':
        data['ordered_scalar_spatial_export']={k:v for k,v in A.items() if k!='theorems'}
        data['ordered_scalar_spatial_lemmas']=[{k:v for k,v in row.items() if k!='dependency_record_ids'} for row in A['theorems']]
    elif name=='OXILEAN_AXIOM_AUDIT.json':
        data['ordered_scalar_spatial_axioms']={row['name']:row['axioms'] for row in A['theorems']}
        data['ordered_scalar_spatial_export_sha256']=A['export_sha256']
    else:
        data['ordered_scalar_spatial_status']='42 proved and independently replayed lemmas; full analytic theorem remains open'
        data['ordered_scalar_spatial_source_sha256']=A['source_sha256']
        data['ordered_scalar_spatial_export_sha256']=A['export_sha256']
        data['spatial_interface_status']='Paper construction and 42 ordered-field spatial semantics lemmas; dense compiler and analytic theorem not Lean formalized'
    p.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    if (M/name).exists(): shutil.copyfile(p,M/name)

counts=A['verdicts']
report=f'''# Lean spatial formalization status

The spatial interface now has **42 new proved lemmas**, all replayed through
the pinned OxiLean checker. The main composition theorem is
`MathCan.SpatialClipped.safe_spatial_stream`. It derives exact vector jet
selection from explicit safe-cell inequalities and bounded stored jets.
The full analytic approximation theorem remains open in Lean.

## Proven spatial statement

Work over an arbitrary scalar type with Lean core's standard `Field`, linear
order, compatible `OrderedRing`, and decidable comparison instances. There
is no custom axiom, admitted proof, assumed address correctness, or assumed
capture correctness. A concrete real-number type and its instances are not
constructed in this stage.

Let K>0 and delta>0. For every coordinate record s, assume

    s.coarse <= n,  s.fine < K,
    c*K+i+delta <= s.position <= c*K+i+1-delta,

where c=s.coarse, i=s.fine, and natural numbers are cast into the scalar field.
The paper's scaled coordinate is u=m*x+1-theta. Coarse ramps at (j+1)*K
recover c exactly; fine ramps after subtracting c*K recover i exactly.
The padded edge block c=n and K=1 are included. All lists and jet dimensions
are arbitrary and finite, including the empty coordinate list.

The explicit triangular ReLU table computes parity at the recovered fine
indices. The normalized snake recurrence uses gate constant 2 and produces
rank/B, B=K^d. Clipping each rank register to [0,1] preserves this value.
The main theorem amplifies it algebraically by B and runs a clipped streaming
capture register for every jet coordinate. If stored jets lie in [-C,C],
C>=0, the output equals exactly the jet at the serpentine rank. Every capture
register stays in [-C,C] for arbitrary scalar inputs, even off the safe set.

Separate boundary-anchor lemmas show that clipping anchors into the domain
preserves local coordinates in [0,1] on safe cells. Thus the spatial algebra
does not require a smooth extension outside the cube.

## Formal modules

| Module | Lemmas | Result |
|---|---:|---|
| `SpatialScalar` | 23 | ReLU, clipping, ramp plateaus, coarse/fine addresses, boundary anchors, one-hot sums |
| `SpatialRouting` | 6 | Three-hinge hats, table reads, snake rank bound and algebraic capture |
| `SpatialNormalized` | 4 | Bounded-gate normalized recurrence, parity lookup, geometric address composition |
| `SpatialClipped` | 9 | Clipped rank and capture invariants; `safe_spatial_stream` |

The older 14 recurrence and integer spatial lemmas remain independently
accepted. There are now 56 research theorem roots across the two corpora.
The unchanged Hodge theorem remains separately accepted.

## Replay evidence

- Lean 4.32.0-rc1: all four modules compile and pass `leanchecker`.
- Preserved project Lean 4.35.0: all four modules compile and pass `leanchecker`;
  its Lean and leanchecker binary hashes remain unchanged.
- OxiLean v0.1.5: **{counts['verified']:,} verified, 0 unsupported, 0 rejected** records.
- Every one of the 42 named theorem roots has an explicit verified verdict,
  and every transitive dependency record verifies.
- Native/reference-parser comparison: all **{A['constants_compared']:,} exported constants**
  have matching names, kinds, universe parameters, types and proof/value terms.
  Only expression metadata and let nondep hints are normalized.
- Export SHA-256: `{A['export_sha256']}`.
- Axiom closure: only `propext`, `Quot.sound`, and `Classical.choice`.
  Each root's exact closure agrees with native `#print axioms`.
- Exporter source: `3de59f10bc4b4a0f2de698597aeb1246caa0df0a`.
- OxiLean source: `3adb983d2aefc6a596bdc8b63438f54feecd1f55`.

`pinned432_spatial/manifest.json` enumerates every new theorem. The acceptance
validator requires equality between that list, the source declarations, native
axiom reports, and verified root verdicts. Eight tamper controls exercise its
refusal of missing verdicts/roots, unsupported dependencies, changed terms or
statements, wrong pins/hashes, and an open dependency graph.

## Remaining proof obligations for the full theorem

1. Instantiate the scalar interface with a formal real field; define the
   C^(k,alpha) unit ball on the cube and prove its Taylor remainder estimate,
   including the integer-smoothness convention.
2. Derive `validSites` records from arbitrary safe shifted-grid inputs, using
   floor indices and the padded boundary blocks. Formalize the multidimensional
   coarse lexicographic address and bounded interpolation circuit that retrieves
   packed words and initial jets.
3. Connect the base-4 sentinel decoder, correction stream, amplitude table,
   and quantized multivariate jet transport to the stored jets used here.
   Existing integer recurrence lemmas supply part of this step.
4. Prove the signed-register-to-dense-ReLU compiler, all carry-wire costs,
   bounded weights and fractional-bit counts. The algebraic amplification by
   B in the selector must be replaced by the staged doubling circuit in that
   compiler proof; this scalar theorem does not certify a weight of B.
5. Prove square/multiplication approximation, clipped polynomial evaluation,
   shifted-grid safe-phase counting and median robustness, then combine the
   error and resource inequalities into the complete approximation theorem.

The finite Python circuit checks and the paper construction remain useful
evidence; they are separate from these Lean proof obligations. No full
analytic/network theorem is exported under a weakened or assumed statement.

## Local reproduction

In the original workspace, set `CAMPAIGN_WORK` to the WSL path of `work/` and run

```bash
bash "$CAMPAIGN_WORK/replay_spatial_scalar432.sh"
python3 "$CAMPAIGN_WORK/test_spatial_acceptance.py"
bash "$CAMPAIGN_WORK/check_spatial_new435.sh"
```

The shell pipeline builds changed modules in dependency order, exports every
manifest root, runs OxiLean with full verdicts, audits dependencies, compares
the native proof terms, and runs the acceptance validator. Reproduction after
restoring the bundle uses the same runtime/exporter paths documented in
`MathCan/research/oxilean_v015/README.md`; copy the included helpers to work/.
Toolchain binaries and compiled oleans are not included in the delivery.

All work remains local. No pushes or messages were sent.
'''
for p in [O/'LEAN_FORMALIZATION_STATUS.md',M/'LEAN_SPATIAL_FORMALIZATION.md',C/'LEAN_FORMALIZATION_STATUS.md']:
    p.write_text(report,encoding='utf-8',newline='\n')
for p in [M/'OXILEAN_V015_REPLAY_REPORT.md',O/'OXILEAN_V015_REPLAY_REPORT.md']:
    old=p.read_text(encoding='utf-8')
    notice='''
Current Lean continuation: 42 additional ordered-field spatial lemmas are
accepted, including exact safe-cell extraction into clipped jet registers.
Read [LEAN_FORMALIZATION_STATUS.md](LEAN_FORMALIZATION_STATUS.md) in the output
packet or `LEAN_SPATIAL_FORMALIZATION.md` alongside this repository report.
The complete analytic/network theorem is still a Lean proof obligation.

'''
    if p.parent==M:
        notice=notice.replace('[LEAN_FORMALIZATION_STATUS.md](LEAN_FORMALIZATION_STATUS.md)',
            '[LEAN_SPATIAL_FORMALIZATION.md](LEAN_SPATIAL_FORMALIZATION.md)')
    p.write_text(old.split('\n',1)[0]+'\n'+notice+old.split('\n',1)[1],encoding='utf-8',newline='\n')
for p in [C/'SPATIAL_INTERFACE_THEOREM.md',C/'QUANTIZATION_D_DIMENSION_THEOREM.md',
          M/'SPATIAL_INTERFACE_THEOREM.md',O/'SPATIAL_INTERFACE_THEOREM.md',O/'QUANTIZATION_D_DIMENSION_THEOREM.md']:
    text=p.read_text(encoding='utf-8')
    text=text.replace('formalized in Lean. The scaled-integer clipping and capture identities are.',
        'formalized in Lean. The integer components and the ordered-field safe-cell\n'
        'address/routing/clipped-capture semantics are now proved and independently\n'
        'replayed. See LEAN_FORMALIZATION_STATUS.md for exact scope and remaining\n'
        'analytic, decoder, and compiler obligations.')
    if p.parent==M:
        text=text.replace('See LEAN_FORMALIZATION_STATUS.md','See LEAN_SPATIAL_FORMALIZATION.md')
    p.write_text(text,encoding='utf-8',newline='\n')
readme=M/'README.md'
readme.write_text(readme.read_text(encoding='utf-8')+'''
## Ordered-field spatial continuation

Read LEAN_SPATIAL_FORMALIZATION.md and pinned432_spatial/ACCEPTANCE.json.
The four additional standalone modules have 42 proved and replayed lemmas;
native Lean 4.32 and preserved 4.35 kernel checks both pass. The full analytic
theorem remains open. For the latest pipeline, copy the included spatial
helpers into CAMPAIGN_WORK, then run replay_spatial_scalar432.sh and
test_spatial_acceptance.py there. The old 14-lemma corpus is retained intact.
''',encoding='utf-8',newline='\n')
print(json.dumps({'new_theorems':42,'research_theorems_total':56,
    'verdicts':counts,'export_sha256':A['export_sha256']},indent=2))
