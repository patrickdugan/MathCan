# ROC-01 registration: recurrent observer report card
Date frozen: **2026-11-16**, before ROC-01 source-generated examples, random-basis draws or checkpoint replay.
Status: prospective measurement protocol; legacy NRF/SPC/OLM reports are **retrospective**, with their original seeds, fitted ranks, and choices preserved. Any protocol change goes in a separately dated amendment.

## Source and comparisons
- Public MathCan parent: `paper/nrf-observable-fibers-v02-20261115` at `2c70886071be263d00976f0cd82f1e44e7b210ec`.
- Original LoopedTransformers source main at `88b99b97f1e8e6d1d5117f5eeaafc841d3639025`.
- Compactification-Theory main at `552bfbceabf34a53fb142b9b854c6a201a0d714b`; EvalMath main `f115865b1bf8cdaca59cae97ff66fcda60e348a2`.
- Six NRF model seeds per depth: `131,137,139,149,151,157`; retain trained depths `16,32`.
- New **prospective** repeat seeds for ROC-01 random bases: `941001..941128` (128 deterministic independent draws per observer per checkpoint/declared state/rank). Seeds apply to the full-source model-state key and are independent of observer-selection data. SPC model seeds are `41522,41523`, with reported held-out prompt seeds preserved.
- Rank grid `k={2,4,8,12,16,32}`. The Part-0 inventory covers originally claimed ranks at most 16; rank 32 is included only for the new price-of-closure sweep. Rank `k>d` is an explicit skip. No tuning rank after viewing ROC-01 effects.
- Fixed prospective regularization: task MSE + `lambda*||B||_F²/||D||_F²`, with `lambda=1.0` as a named reference. Publish full lower envelope over `lambda≥0`; exploration grid `{0,0.05,0.2,1.0,2.0}`. Historical NRF chosen gamma belongs to the old experiment and is preserved unchanged.
- Observer optimizer: mirror the **same initialization, optimizer steps, train data, QR schedule and decoder head** in a penalty-free task-only comparator for every fitted observer. For the historical NRF comparison this means 80 Adam updates, LR 0.02 and the same rank-eight start. Any genuinely new model gets a model-specific optimizer lock before fit and a logged task-only twin.
- Causal source: frozen checkpoint and state-ID; output Jacobian `J_i` must be of the **declared output at the declared horizon**, not an arbitrary head. Causal Gram `H=Σ_i w_i J_i^T J_i`, with `w_i>0, Σ w_i=1` (OLM-07). Freeze weights, output choice and held-out state list. Mark `s` undefined when `tr H=0`.

## Per-state ROC card
At the state `h`, let `T=D(F^n)(h)`, `D=T-I_d`, `U ∈ R^{d×k}` orthonormal and `Q` an orthonormal basis for `im(I-UU^T)`:
- `A=U^T D U` (**within**), `B=U^T D Q` (**dark→observed**), `C=Q^T D U` (**observed→dark**).
- Publish raw `||A||F,||B||F,||C||F` and normalized `a=||A||F/||D||F`, `b=||B||F/||D||F`, `c=||C||F/||D||F`. Also publish per-observed-coordinate values `||A||F/sqrt(k)`, `||B||F/sqrt(k)`, `||C||F/sqrt(k)`. If `||D||F=0`, a=b=c=0 **with an explicit zero-dynamics flag**; `s=tr(U^T H U)/trH`.
- Publish task MSE **for the same state, frozen task decoder, and target**, or `null` with `task_mse_available=false`. Do not equate pooled published MSE with a per-state measurement.
- Include `d,k,rank(D),n,checkpointSHA,observerSHA,stateID,output_horizon,basis_selection,seed,split,classification` and per-state source row hashes.
- These types are **nonexclusive diagnostic tags**, not an exhaustive classification. Pre-registered thresholds applied to normalized `a,b,c`: near-zero `≤0.05`; large `≥0.20`. Causal capture high `s≥0.80`, low `s≤0.20`. Tags:
  - closed quotient if b near-zero;
  - invariant/driver if c near-zero;
  - latched memory if a,b near-zero and s high;
  - output register if b large, a,c near-zero;
  - irrelevant if a,b near-zero and s low.
  Diagnostic `unclassified` is allowed; a card can have multiple tags.

## Nulls, comparisons and reporting
For **each checkpoint/state/k/observer**, score **128** seeded rank-k random Haar/QR bases on the identical `D,H,h,task` measurement. Report each metric's random median, 5th/95th percentile, rank and empirical one-sided p `(1+#{random values at least as extreme})/129`. For smaller B, use lower tail, for larger s or task improvement upper tail; state the direction before running. Use Holm adjustment across the five diagnostic metrics per hypothesis family. Z-scores are descriptive and never p-values.
For every intervention, include **at least one independently seeded equal-initial-L2-radius random direction** on the same state/position/pass. Record actual post-step L2 displacement and readout leakage. An arm failing radius/readout parity is marked invalid and cannot contribute a causal gate.
For six NRF model seeds, publish **six paired differences**, their mean/median, and counts `k/6` for every winner claim. For SPC's two trained checkpoints, report `k/2`; no claim of six independent seeds.
Historical results with 8 random bases (NRF-10/11, SPC-05, SPC-08) remain labeled **insufficient for ROC statistical gate**. They are not promoted by changing the p calculation.

## T-C identification and T-D tradeoff
- Candidate mechanisms: closed quotient, invariant/driver, latched memory, output register, irrelevant. Candidate interventions: dark→observed donor transplant, observed→dark donor transplant, freezing U-coordinate, ablating U at readout; **each** has a norm-matched random arm.
- Use measured categorical outcome distributions to compute BPD-01 minimum-cost separating test collection; unknown routes remain unknown. Use measured repeat outcome variances for the Chernoff max-min KL allocation, reporting any observationally equivalent pair. Synthetic demonstration signatures must be labeled hypothetical and cannot be used as neural evidence.
- For the objective `E + lambda L`, derive all pairwise equality points, remove dominated candidates, and report the actual lower envelope. Extend to the (rank, task error, normalized ||B||) Pareto surface with no scalarization claimed to determine a unique winner.
- Random-basis and outcome seeds locked here. No headline/new checkpoint experiment before Parts 0–2 are committed and the exact-rational checks, literature review and Lean scope ledger are public.

## Claim boundaries
Missing weights, observer adapters, state Jacobians or per-state task rows are **not equivalent to zero**. A script plus public per-state rows must accompany each new CSV in MathCan. Every open counterexample precedes its positive theorem. Lumpability/observability and balanced-truncation bounds get conventional attribution.
