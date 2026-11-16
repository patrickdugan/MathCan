# ROC-01: Fable public review packet

**Date:** 2026-11-16. **Status:** Parts 0–4 committed in public MathCan.
**Publication mode:** source-linked calculation, retrospective NRF v0.4 data,
and finite synthetic theory controls. Numerical NRF/SPC checkpoint replays
remain blocked by unavailable public model/adapter matrices. The original
NRF checkpoint and task reports are preserved.

Public source base: MathCan NRF v0.4 branch
`paper/nrf-observable-fibers-v02-20261115` at
`2c70886071be263d00976f0cd82f1e44e7b210ec`.
The paired observer calculus lives in `research/observer_calculus/`.
Registration was committed first, before derived CSV generation.

## Part 0: inventory

| Evidence | Completed | Still missing |
|---|---|---|
| [Pinned rank<=16 inventory](PART0_INVENTORY.md), across MathCan, EvalMath, LoopedTransformers, Compactification-Theory | NRF-04,06,07,08X,09,10,11; SPC-05–08; TRM rank-11 head; OLM/SMC SAE atoms; discrete COE and EvalMath distinctions. Basis-choice/null/k-selection and status recorded, NRF-04 corrected to k=8 from its frozen config. | Full automated scan of every historical branch and the external .pt/adapter archives. A source document is not evidence that its model tensor was independently replayed. |

## Part 1: observer card

| Evidence | Completed | Still missing |
|---|---|---|
| [ROC card](observer_card.py), [registration](ROC01_REGISTRATION.md), 128 seeded basis nulls and gauge-control tests | For declared T,U,H computes A=U^T(T-I)U, B=U^T(T-I)Q, C=Q^T(T-I)U, s=tr(U^THU)/trH and normalized norms. Synthetic register/latch/irrelevant examples; exact reproducibility. The historical [1,584 per-state NRF11 partial rows](ROC01_NRF11_PER_STATE_PARTIAL.csv) preserve known A/B/C per sqrt(k). | Existing neural per-state full norm of T-I, causal H, per-state decoder MSE, >=100 random nulls and matched physical intervention arm results. These remain null, with invalid rank-p flag and retrospective status. |

## Part 2: mathematical evaluation

| Target | Checked proof or counterexample first | Lean / quantitative boundary |
|---|---|---|
| T-A rank floors | Rank-one x+2y separates four Q² states; exact linear decoder requires k>=rank(G); precision b gives k>=ceil(log2 N/b). | Lean Bool×Bool finite injection; general real matrix rank floor written. |
| T-B closure | Smallest invariant readout-containing W is the span of (T^T)^j G^T. Rotation T=diag(1,R90), G=e1^T yields L*(1)=0,L*(2)=1,L*(3)=0. 540 exact rational d<=6 finite-horizon bounds passed. | Finite observability singular-tail gives **lower**, not upper, bound on L*(k). [Source-only sampled closure sweep](closure_sweep.py) yields lower bound plus 128-sample upper bound; full real statement written, Lean general theorem pending. |
| T-C type discrimination | Hypothetical five-type four-arm table has exact three-arm BPD-01 cover. With Gaussian unit-variance binary means, **optimal KL allocation uses four arms**, (1,1,2,1)/5; min KL=1/5, so noiseless cover and statistical allocation differ. | Fraction grid and exact upper bound; [Lean integer-scaled witness](../../MathCan/ObserverChernoff.lean) checked. Actual neural type effects, Chernoff means/variances and source routes absent. |
| T-D tradeoff | Exact fractional lower-envelope and nondominated rank/error/B surface code. | Public NRF v0.4 raw-leakage switches at 0.136474,0.875804,1.242665,1.391717. New normalized-B rank sweep pending. |

See [Part-2 counterexamples, proofs and literature](PART2_THEORY.md).
Balanced-truncation Hankel-error results and classical Kalman observability
precede this application. No general model-reduction theorem priority claimed.

## Part 3: NRF v0.4 carry-over

| Observation | Recomputed public measurements | Source |
|---|---|---|
| Depth-32 NRF11, six matched model seeds | Mean delta B=-0.195247, with magnitude contribution -0.161737 and fractional contribution -0.033510; B falls 6/6, magnitude 6/6, fraction 5/6. Seed 131 fraction increases +0.037346 while B decreases -0.279992. | [All 12 per-seed/depth records](ROC01_NRF11_PER_SEED_DECOMP.csv), [source generator](nrf_retrofit.py), [summary](ROC01_NRF11_SUMMARY.json). |
| Depth-16 NRF11 | Mean delta B=-0.060531, magnitude -0.047311, fraction -0.013220; each reduction 6/6. | [Part 3 full per-seed table](PART3_NRF_V04_CARRYOVER.md). |
| Historical Table 4 | Pairwise task-only break-evens differ from lower-envelope switchpoints, which are 0.136474,0.875804,1.242665,1.391717 using raw squared leakage. | [Updated v0.4 paper](../../papers/NRF_Observable_Fibers_Revised_v04.md) Table 3C, 4 and 4B; [exact fractional envelope](frontier.py). |

The paired decomposition is algebraic and **retrospective**. It is not a
randomized test of the penalty's causal mechanism. No new neural weight
training or held-out model cohort ran here.

## Part 4: next registration

| Field | Frozen prospective choice | Executed? |
|---|---|---|
| New task | Delayed-rule binding/release with distractor overwrites and exact verifier; recurrent tied width-128 model, six new seeds | **No new samples or training** |
| Rank / observer selection | k={2,4,8,12,16,32}; fixed task-only comparison, PCA, Gramian and leakage-aware candidates; 80 equal-budget optimizer steps | Registered only |
| Card / random and intervention endpoints | A/B/C normalized, s, task MSE; 128 rank-matched random bases seeds 941001..941128, matched causal random arm per intervention; registered three-arm T-C set plus readout-ablation control | Registered only |
| Source/confirmation | Train/calibration/sealed split seeds 2026111621/23/27, five-family Holm p gates, per-seed paired k/6 outcomes and exact symbolic baseline | Registered, test sealed |

[Prospective Part-4 registration](PART4_NEXT_REGISTRATION.md) preserves
source/seed and readout contracts before new task generation.

## Evidence checklist

**Ran:** 128-basis synthetic-card null tests, synthetic rank sweep, exact
rational Fraction oracles, inherited NRF v0.4 source-level reproducibility,
1,584-row source CSV replay and 12 NRF seed decompositions, finite Lean
witnesses and synthetic Chernoff LP bound. Source and per-state data are in
this **public** MathCan branch.

**Did not run:** fresh NRF/SPC weights, empirical per-state OLM-07 H on those
neural checkpoints, rank-k global closure optimization on existing neural
states, the new delayed-rule task, causal transplant outcome distributions,
or a real neural Chernoff allocation. All are explicit future gates.

The companion EvalMath evaluator routes the synthetic four-arm table
through BPD-01 T1 with source/checkpoint/route validation and refuses
promotion of incomplete cards. Fable can reproduce the reported public
source results without access to private conversation artifacts.
