from pathlib import Path
import hashlib
import json
import shutil

W=Path(__file__).resolve().parent
O=W.parent/'outputs'
M=W/'MathCan/research/oxilean_v015'
C=W/'Compactification-Theory/research/quantization'
R=W/'replay432/Decoder'
N=W/'replay435/Decoder'
A=json.loads((R/'ACCEPTANCE.json').read_text(encoding='utf-8'))
F=json.loads((C/'decoder_trace_fixture_results.json').read_text(encoding='utf-8'))
assert A['status']=='accepted' and len(A['theorems'])==39
assert A['verdicts']['unsupported']==A['verdicts']['rejected']==0
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,digest in A['source_sha256'].items(): assert sha(W/'MathCan'/rel)==digest
receipt={'status':'passed','native_and_leanchecker_432':'accepted','native_and_leanchecker_435':'accepted',
    'source_sha256':A['source_sha256'],
    'imported_spatial_source_sha256':json.loads((W/'replay432/SpatialScalar/ACCEPTANCE.json').read_text())['source_sha256'],
    'preserved_435_binary_hashes':(N/'preserved_binary_hashes.txt').read_text(),
    'olean_sha256_432':{m:sha(R/'lib/MathCan'/f'{m}.olean') for m in ['SentinelDecoder','DecodedJetCapture']},
    'olean_sha256_435':{m:sha(N/'lib/MathCan'/f'{m}.olean') for m in ['SentinelDecoder','DecodedJetCapture']},
    'exporter_binary_sha256':sha(W/'replay432/lean4export-source/.lake/build/bin/lean4export'),
    'oxilean_binary_sha256':sha(W/'build/oxilean-verify')}
(R/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
target=M/'pinned432_decoder'
target.mkdir(parents=True,exist_ok=True)
for p in R.iterdir():
    if p.is_file() and p.suffix in {'.json','.log','.lean','.txt','.ndjson','.sha256'}:
        shutil.copyfile(p,target/p.name)
compat=target/'compat435'
compat.mkdir(exist_ok=True)
for p in N.iterdir():
    if p.is_file(): shutil.copyfile(p,compat/p.name)
for name in ['check_decoder432.sh','check_decoder435.sh','run_decoder_replay432.sh',
             'prepare_decoder_replay.py','accept_decoder432.py','test_decoder_acceptance.py',
             'validate_decoder_final.py','finalize_decoder_campaign.py','package_decoder_results.py']:
    shutil.copyfile(W/name,M/name)
for name in ['decoder_acceptance','decoder_acceptance_controls','retained_spatial_acceptance','decoder_trace_fixture']:
    shutil.copyfile(W/'logs'/f'{name}.log',target/f'{name}.log')
shutil.copyfile(O/'FINAL_VALIDATION.json',M/'FINAL_VALIDATION.json')
shutil.copyfile(R/'ACCEPTANCE.json',O/'DECODER_LEMMAS_ACCEPTANCE.json')
for name in ['SentinelDecoder.lean','DecodedJetCapture.lean']:
    shutil.copyfile(W/'MathCan/MathCan'/name,O/name)
for name in ['decoder_trace_fixtures.jsonl.gz','decoder_trace_fixture_results.json']:
    shutil.copyfile(C/name,O/name)
v=A['verdicts']
report=f'''# Sentinel decoder and spatial jet capture: Lean continuation

2026-11-16, Asia/Taipei. **39 new theorem roots are proved and independently
replayed.** There are now 95 research theorem roots across the three corpora;
Hodge remains a separate unchanged theorem. The full analytic approximation
theorem is still open.

## What is now proved

`SentinelDecoder.word` encodes a Boolean payload followed by a trailing digit-one
sentinel: word([])=1/4, word(b::tail)=(1+bit(b)+word(tail))/4. The scalar field
is arbitrary subject to Lean core's standard ordered-field classes, as in the
previous spatial proofs. These statements do not construct a concrete real type.

1. Every suffix lies in [1/4,2/3]. The exact two-hinge reader
   4*(ReLU(4*z-7/4)-ReLU(4*z-2)) returns the leading payload bit. Clipping the
   suffix update 4*z-1-readBit(z) into [0,1] preserves the encoded tail.
2. All payload bits, concatenated prefixes, and frame boundaries decode exactly.
   After all S payload reads, the sentinel remains at 1/4. The theorem does not
   treat an additional sentinel read as a payload read. Empty payloads and empty
   frames are covered.
3. At each valid read, a two-sided perturbation of magnitude at most 1/48 leaves
   the bit exact and changes the suffix error by exactly a factor of four.
   `noiseBudget(0)=1/48`, `noiseBudget(S+1)=noiseBudget(S)/4` gives a sufficient
   full-payload input budget. This is 1/(48*4^S); it is a conservative budget.
   Prefix and frame theorems propagate the remaining budget explicitly.
4. The terminal suffix error equals 4^S times the initial code error. This is a
   sensitivity result, not length-independent numerical stability. No theorem
   here covers arbitrary fresh arithmetic noise at every recurrent update.
5. The encoded word times 2^(2*(S+1)) is an integer numerator, which lies below
   4^(S+1). Thus 2*(S+1) binary fractional slots suffice for the stored word.
   This statement concerns representation of the parameter, not noise tolerance
   of activations or the total precision budget of the network.
6. Little-endian payload integers and signed corrections decode exactly.
   A finite matrix-plus-correction update constructor is supplied. More generally,
   every deterministic finite-dimensional update receives exactly the same frame
   bits in the reference and decoded recurrences. Coordinatewise clipping bounds
   every resulting jet state and preserves states already in the allowed range.

## Connection to spatial capture

The main roots are `MathCan.DecodedJetCapture.decoded_spatial_capture` and
`MathCan.DecodedJetCapture.robust_decoded_spatial_capture`.

For valid safe-cell records, the earlier spatial circuit extracts fine indices,
reads parity, and computes the clipped normalized serpentine rank. If the number
of payload frames is B-1 for B=K^d sites, that rank selects an actual jet state in
the frame stream, including the initial state. The sentinel decoder supplies
each frame directly from the one packed word. The captured vector is exactly
the corresponding reference clipped jet state, including under the stated
initial code perturbation budget. No decoder-correctness premise or external
jet-bound premise is substituted for this composition: bounds follow from the
initial-state bound and the clipped updates.

The update function is a parameter of the semantic theorem. The provided matrix
constructor makes finite matrix transport plus correction an instance; proving
that the particular Hamming amplitude selector and Taylor transport matrix
implement the paper's quantized jet remains a separate obligation. This does
not establish the full Taylor approximation or a dense ReLU resource bound.

## Verification

- Lean 4.32.0-rc1: both modules compile and pass `leanchecker`.
- Preserved Lean 4.35.0: both modules compile and pass `leanchecker`; original
  Lean and leanchecker binary hashes are unchanged.
- OxiLean v0.1.5: **{v['verified']:,} verified, 0 unsupported, 0 rejected** declarations.
- All 39 named new roots and their complete dependency closures verify.
- All **{A['constants_compared']:,} exported constants** match native names, kinds,
  universe parameters, types and proof/value terms. Only metadata and let nondep
  hints are normalized, with no proof substitution or reduction.
- Export SHA-256: `{A['export_sha256']}`.
- Native and exported root axiom inventories agree: only `propext`, `Quot.sound`,
  and `Classical.choice`. There are no admitted declarations or custom axioms.
- All eight acceptance tamper controls pass. Source hashes are checked before
  and after the pipeline, and the previous four spatial sources remain unchanged.
- Exporter source: `3de59f10bc4b4a0f2de698597aeb1246caa0df0a`.
- Checker source: `3adb983d2aefc6a596bdc8b63438f54feecd1f55`.

The complete manifest, per-declaration verdicts, root closures, native logs,
source comparison and acceptance data are in `pinned432_decoder/` in MathCan.
The prior Hodge, 14-lemma and 42-lemma artifacts remain separate historical runs.

## Contribution to looped-transformer mechinterp and guided training

The direct contribution is now a checked specification and concrete reference
data: **95 generic research theorem roots**, plus **{F['positive_examples']} positive
decoder trace fixtures**, one no-sentinel negative control and **{F['decoded_steps']:,}
exact decoder steps**, with payload lengths through {F['maximum_payload_length']}.
The register and signed-pair ReLU evaluators agree at every fixture step. The
fixtures include split labels for training-pipeline development, calibration,
and longer-length checks. They are public fixtures, not a sealed evaluation set.
The serializer/data loader itself has not been Lean verified.

The shared-transition and state-factorization framing matches the program's
[looped/TRM/LDT taxonomy](https://github.com/MoralityLabAI/HybridTRMLDT/blob/e412e84131548e5b0c7534bd6f440a9089962b73/docs/looped_transformer_trm_ldt_taxonomy.md).
The current [looped-mechinterp paper](https://github.com/MoralityLabAI/LoopedTransformers/blob/88b99b97f1e8e6d1d5117f5eeaafc841d3639025/papers/rmp_looped_mechinterp/main.tex)
already frames interpretation in terms of repeated invocations and exact task
traces. The proposed connection is to use named code, suffix, correction, jet,
and capture registers as intermediate supervision and causal-intervention
targets, indexed by recurrent visit and computational phase.

No transformer training job, improved accuracy, recovered neural mechanism or
transfer effect was demonstrated in this continuation. A useful next experiment
compares output-only supervision with transition/invariant guidance at matched
compute, freezes an independent length-generalization set, and checks whether
interventions transfer the named state variables. A learned mechanism must be
tested separately from correctness of its reference algorithm.

## Remaining approximation obligations

- Derive safe-cell records from all safe shifted-grid points and formalize
  multidimensional coarse lookup of the packed word and initial jets.
- Specialize frame parsing to displacement/amplitude and all J correction windows;
  prove the Hamming selector, actual Taylor transport and correction-size bounds.
- Supply real-field/analytic foundations, Taylor remainder and polynomial-network
  error estimates, safe-phase counting and median stitching.
- Prove dense compiler correctness, staged selector amplification and all weight,
  depth, parameter and precision budgets.

## Reproduction and publication

Set CAMPAIGN_WORK to the original WSL work/ path and run

```bash
bash "$CAMPAIGN_WORK/run_decoder_replay432.sh"
python3 "$CAMPAIGN_WORK/test_decoder_acceptance.py"
bash "$CAMPAIGN_WORK/check_decoder435.sh"
```

The user authorized publication of the existing research branches on 2026-11-16.
Exact pushed heads are verified separately in the output `PUSH_RECEIPT.json`.
The follow-up to Tetsuya is an unsent draft; no email or repository comment was sent.
'''
for p in [O/'DECODER_FORMALIZATION_REPORT.md',M/'DECODER_FORMALIZATION_REPORT.md',C/'DECODER_FORMALIZATION_REPORT.md']:
    p.write_text(report,encoding='utf-8',newline='\n')
draft=f'''# Follow-up to Tetsuya — draft only, not sent

Subject: Independent kernel replay, sentinel decoding, and recurrent-state training traces

Hi Tetsuya,

I’ve pushed a repository-first update to the research branches:

- [MathCan proofs and replay evidence](https://github.com/patrickdugan/MathCan/tree/research/quantized-jet-replay-20261115)
- [Approximation construction and reference traces](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/quantization-d-audit-20261115)

The unchanged Hodge theorem now passes the pinned Lean 4.32/exporter/OxiLean
pipeline: 1,256 verified declarations, no unsupported or rejected declarations.
The earlier toolchain blocker is resolved.

The latest addition is 39 proved lemmas connecting base-4 sentinel decoding to
clipped spatial jet capture. Its dependency-closed replay gives {v['verified']:,}
verified declarations and zero unsupported/rejected declarations; all
{A['constants_compared']:,} exported types and proof/value terms match the native
environment. The axiom inventories are explicit: propext, Quot.sound and
Classical.choice. Both the pinned 4.32 checker and the preserved 4.35 checker pass.

The decoder recovers concatenated payload frames exactly, retains the sentinel,
and has a proved 1/48 per-read margin. It needs 2(S+1) fractional slots to store
S payload bits. Code-state error grows by 4 per read, so the full-payload
robustness guarantee uses a length-dependent input budget; this is not a claim
of arbitrary-precision recurrent stability. Composing it with the spatial
address/rank proof gives the same selected clipped jet as the reference updates.
The full smooth approximation theorem still needs the particular amplitude/Taylor
transport specialization, analytic estimates, and dense compiler/resource proof.

This applied-math work is feeding our looped-layer transformer program at the
specification and reference-data level: we now have 95 generic research theorem
roots, and this continuation adds 144 positive trace fixtures, one no-sentinel
negative control, and 1,896 exact decoder steps through payload length 64.
Both circuit evaluators agree on every step. The fixtures currently label code,
read bits and suffix states. The proved correction, jet-update and capture
semantics define further candidate supervision and intervention targets,
indexed by recurrent visit and computational phase.

We have not yet shown that this guidance improves a trained transformer or
identifies its learned mechanism. The next controlled comparison is output-only
versus transition/invariant-guided training at matched compute, with independently
held-out lengths and interventions on those named states. The mathematical
reference being correct is one layer of evidence; the learned recurrence still
needs its own causal tests.

I’d value an independent attempt to break the decoder/capture composition or
its replay assumptions. The manifest, exact export hash, axiom closures and
per-declaration verdicts are in MathCan’s `research/oxilean_v015/pinned432_decoder/`.
A written repository exchange works well for me.

Patrick
'''
for p in [O/'TETSUYA_FOLLOW_UP_DRAFT.md',O/'TETSUYA_PROPOSED_EXCHANGE.md',
          M/'TETSUYA_PROPOSED_EXCHANGE.md',C/'TETSUYA_PROPOSED_EXCHANGE.md',W/'TETSUYA_PROPOSED_EXCHANGE.md']:
    p.write_text(draft,encoding='utf-8',newline='\n')
notice='''
Decoder continuation (2026-11-16): 39 additional lemmas prove exact/robust
sentinel decoding and its composition with clipped spatial jet capture.
See DECODER_FORMALIZATION_REPORT.md for the current 95-root research status,
trace fixtures and remaining obligations. Publication of the research branches
is now authorized; the earlier local-only statements below describe the prior run.

'''
for p in [O/'LEAN_FORMALIZATION_STATUS.md',M/'LEAN_SPATIAL_FORMALIZATION.md',C/'LEAN_FORMALIZATION_STATUS.md',
          O/'OXILEAN_V015_REPLAY_REPORT.md',M/'OXILEAN_V015_REPLAY_REPORT.md']:
    text=p.read_text(encoding='utf-8')
    if 'Decoder continuation (2026-11-16)' not in text:
        title,rest=text.split('\n',1)
        p.write_text(title+'\n'+notice+rest,encoding='utf-8',newline='\n')
for p in [M/'README.md',C/'SPATIAL_INTERFACE_THEOREM.md',C/'QUANTIZATION_D_DIMENSION_THEOREM.md',
          M/'SPATIAL_INTERFACE_THEOREM.md',O/'SPATIAL_INTERFACE_THEOREM.md',O/'QUANTIZATION_D_DIMENSION_THEOREM.md']:
    text=p.read_text(encoding='utf-8')
    if 'Decoder continuation (2026-11-16)' not in text:
        title,rest=text.split('\n',1)
        p.write_text(title+'\n'+notice+rest,encoding='utf-8',newline='\n')
for name in ['OXILEAN_DECLARATION_VERDICTS.json','OXILEAN_AXIOM_AUDIT.json','PROVENANCE.json']:
    p=O/name
    data=json.loads(p.read_text(encoding='utf-8'))
    if name=='OXILEAN_DECLARATION_VERDICTS.json':
        data['sentinel_decoder_export']={k:x for k,x in A.items() if k!='theorems'}
        data['sentinel_decoder_lemmas']=[{k:x for k,x in row.items() if k!='dependency_record_ids'} for row in A['theorems']]
    elif name=='OXILEAN_AXIOM_AUDIT.json':
        data['sentinel_decoder_axioms']={row['name']:row['axioms'] for row in A['theorems']}
        data['sentinel_decoder_export_sha256']=A['export_sha256']
    else:
        data['decoder_continuation']={'date':'2026-11-16','new_roots':39,'research_roots_total':95,
            'export_sha256':A['export_sha256'],'source_sha256':A['source_sha256'],
            'publication_authorization':'User explicitly requested pushes of the research work; follow-up prepared only, not sent.'}
    p.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    if (M/name).exists(): shutil.copyfile(p,M/name)
print(json.dumps({'new_roots':39,'research_roots_total':95,'verdicts':v,
    'draft':'prepared, unsent','fixtures':F['positive_examples']},indent=2))
