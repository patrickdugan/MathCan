# ROC-01 Fable review report: one calculus for low-rank recurrent observers

**Dated 2026-11-16.** Repository: patrickdugan/MathCan, branch research/roc01-unified-observer-card-20261116, extending public NRF v0.4 parent commit 2c70886071be263d00976f0cd82f1e44e7b210ec. Parts 0–2 were publicly committed before the later NRF retrofit and ROC-02 registration. This is a source review report; neural checkpoints not present in public Git are **not** assumed to exist.

> **Dated prospective amendment 2026-11-16C:** [ROC01_AMENDMENT_2026-11-16C.md](ROC01_AMENDMENT_2026-11-16C.md) replaces the old diagnostic thresholds with rank-conditioned null scores, replaces the physically confounded freeze arm by observed→observed, and adds ranks 1, 3 and SPC 7. Sections below retain their original historical review context; they are not the amended ROC-02 protocol. The corrected original freeze design cannot identify the invariant/register pair.

### Open counterexamples placed before proofs

- Finite separation cannot force k>1 without a decoder/precision/closure contract: four distinct rational 2D points have unique scalar codes x+2y.
- Exact-rank closure cost is not rank-monotone: for a 3D matrix fixing e1 and rotating its orthogonal two-plane by 90 degrees, rank-one and rank-three closed observers exist, while **every** rank-two observer containing readout e1 has incoming leakage norm one. Thus L*(1)=0, L*(2)=1, L*(3)=0.
- A low output-coupling ratio can arise from small observed writes. Within the same NRF-11 models, absolute B falls in 6/6 seeds, while the dark fraction falls only in 5/6.
- A nonadaptive minimum test collection need not be a statistical optimum: the synthetic five-type table has a **three-arm** separating cover but an exact four-arm Gaussian max-min allocation (1/5,1/5,2/5,1/5).

The proofs, exact rational searches, literature attribution and Lean claim limits follow in Part 2 and the dated amendment. These are classical algebraic/systems tools specialized to the evaluation interface, with independent mathematical priority unestablished.

## Part 0: source inventory

| Audited group | d, k | Selection and measured quantity | Random/null status and missing evidence | Source |
|---|---|---|---|---|
| NRF-04/06/09 | d=128; rank 8/16 | learned or supervised QR/PCA-type observers; MSE, leakage, quotient gate | eight rank-matched historical random arms, no unified per-state causal Gram | LoopedTransformers pinned main |
| NRF-10/11 + v0.4 | d=128,k=8; depths 16,32, six seeds/depth | equal-budget task-only and leakage penalized QR observer; full B,C,A state-local change blocks in v0.4 | 1,584 existing per-state rows now mirrored; full D,H,task-per-state, 128 null bases and .pt bytes absent | MathCan NRF paper branch |
| SPC-05/06/07/08 | d=48,k={2,4,7,8,12,16} | phase increment PCA, immediate/deferred Gramian and Procrustes; phase transplants/freeze | 4–8 historical random arms; full .pt weights and per-state Jacobian matrices externally archived | LoopedTransformers pinned main |
| TRM LOOPSCOPE-02/03 | 512-wide board state, rank-11 lm_head | exact head-row readout, 501D dark complement, cache/refill and solve changes | random subspace and full unified state cards not available | LoopedTransformers pinned main |
| OLM-07/14 and SMC | 48-wide reported teacher; one SAE feature per probe | causal Gram energy and finite-radius SAE feature effects | inactive/isotropic/mapping controls; one direction is not globally sufficient state compression | MathCan OLM notes |
| COE and EvalMath | finite codes / 24-wide temporal toy / exact symbolic quotients | graph-edge code separation, temporal bits, verifier-preserving quotients | mathematically different object from d×k orthonormal linear U; card tagged not-a-linear-observer | Compactification-Theory and EvalMath |

What ran: pinned public document/receipt inventory with source and null classification. What did not: exhaustive historical branch/archive search; replay of externally archived trained .pt checkpoints. The complete source-path table is in PART0_INVENTORY.md.

## Part 1: observer report card

| Endpoint | Definition and implementation | Existing result | Gate still open |
|---|---|---|---|
| Within computed change A | Uᵀ(T-I)U; raw, /sqrt(k), /||D||F | NRF-11 original per-state within/sqrt8 imported | full D norm needed for normalized card |
| Incoming B / outgoing C | Uᵀ(T-I)Q and Qᵀ(T-I)U | 1,584 NRF-11 per-state original B,C/sqrt8 rows source checked | SPC per-state checkpoint replay and 128 rank-k null distributions |
| Causal capture s | tr(Uᵀ H U)/tr(H), H from declared output Jacobians | working pure-Python reference, exact register/latch/irrelevant witnesses | per-state neural H and task MSE absent |
| Diagnostic type | closed if B≈0, invariant if C≈0, latch if A≈B≈0 and s high, register if B large/A,C near zero, irrelevant if A≈B≈0 and s low | synthetic nonexclusive type test passed | thresholds apply prospectively, not retrospectively to partial cards |
| Null/causal intervention | 128 keyed QR bases with rank-add-one p and Holm; separate L2-matched random *intervention* | synthetic same-state reference and conditional closure sweep tests passed | old 8-arm neural null cannot yield new valid p; new matched arms still to run |

A T-B readout-constrained random completion is a **different** sample space from the full-card rank-k Haar null. The dated amendment makes the conditional-null rank p undefined when k=rank(G), k=d, or every tested B is identical. The original registration remains intact.

## Part 2: evaluation mathematics and scope

| Target | Counterexample or positive result | Check actually run | Pending |
|---|---|---|---|
| T-A rank forcing | rank-one separates any finite distinct real-state set; exact linear all-state decoder forces k≥rank(G); fixed-b precision forces k≥ceil(log2(N)/b) | four-code rational witness and narrow Lean Bool injectivity | domain-specific neural lower-rank observer or a checked task-decoder floor for every Part-0 claim |
| T-B closure price | unique minimum closed rowspace span{Gᵀ,TᵀGᵀ,...}; L*(k) can be nonmonotone in exact k; finite-horizon observability singular tail gives a lower bound on L*(k) | 540 exact-rational matrix instances at d≤6, 3D rotation, finite Lean examples, NumPy conditional 128-basis synthetic sweep | actual NRF/SPC k={2,4,8,12,16,32} checkpoint matrices and measured global/approximate L* |
| T-C probe identification | idealized five-type T1 cover requires three arm classes; Gaussian unit-variance max-min KL=1/5 uses all four at weights 1/5,1/5,2/5,1/5 | Fraction table exhaustive cover, exact inequality, narrow Lean integer-scaled proof | repeated measured interventions with matched random controls, route data and none-fits model |
| T-D exchange rates | exact rational lower envelope over fixed candidates and nondominated (rank,error,B) surface | NRF v0.4 retrospective raw-unit switches 0.136474,0.875804,1.242665,1.391717 independently checked | corresponding *normalized-B* rank/error/leakage surface from checkpoints |

Literature checked: Kalman observability/invariant subspaces, Moore (1981) internally balanced realization, and classical balanced-truncation error bounds involving *Hankel* singular values. Their assumptions and quantities differ from local ROC incoming-block leakage. Real-matrix and singular-value theorems are written proofs; Lean proves named finite specializations only. The allocation bound has propext and Quot.sound in the Lean axiom inventory through omega; ordinary kernel checks pass without sorry.

## Part 3: NRF v0.4 retrospective carry-over

Six-seed paired decomposition from the actual 12 shadow states per model on NRF-11 fold 13. B equals observed write magnitude W times incoming fraction rho, with exact per-state symmetric decomposition. The gamma column is the **original frozen selected** gamma; all numbers below are post-hoc.

| Depth-32 seed | Selected gamma | ΔB joint minus task | Write-magnitude contribution | Fraction contribution |
|---:|---:|---:|---:|---:|
| 131 | 1.0 | -0.27999 | -0.31734 | +0.03735 |
| 137 | 0.2 | -0.13659 | -0.08780 | -0.04879 |
| 139 | 0.2 | -0.16442 | -0.09583 | -0.06859 |
| 149 | 1.0 | -0.28805 | -0.26905 | -0.01899 |
| 151 | 0.2 | -0.13772 | -0.09831 | -0.03941 |
| 157 | 0.2 | -0.16472 | -0.10209 | -0.06263 |
| Six-seed mean | mixed | -0.19525 | -0.16174 | -0.03351 |

Write magnitude explains 82.8% of the mean drop under this *algebraic* accounting; B decreases 6/6 and proportional fraction decreases 5/6. The manuscript's depth paragraph and conclusion center the large initialized coupling and observed write magnitude, and Table 4B distinguishes actual pooled lower-envelope switches from task-only pairwise crossovers. The 0.624 (NRF-10) and 0.567 (NRF-11) selected-gamma break-evens remain in the **old raw leakage units**.

What ran: deterministic public-CSV regeneration of all 1,584 partial state cards, twelve per-seed decomposition rows, and exact-fraction envelope switches. What did not: new model training, a new 128-basis neural null, or neural H/task-per-state estimation.

## Part 4: frozen next experiment

| Design dimension | Registered value | Intended outcome and open dependency |
|---|---|---|
| Task | new delayed-rule binding with distractor rewrites; independent symbolic interpreter; unknown/no-rule cases | isolate hidden rule-carry and output-register roles, beyond signed-permutation and pointer graphs |
| Model/data | tied residual 128-channel recurrent MLP; six model seeds 2026111601,03,07,09,13,19; train/cal/test seeds 2026111621/23/27, 1024/256/384 records | source/structure-disjoint heldout, no fitting on sealed test |
| Ranks/objective | 2,4,8,12,16,32; task-only twin 80 Adam/QR updates, lambda=1 ROC objective plus declared grid {0,.05,.2,1,2} | per-rank full (MSE,A,B,C,s) state card, Pareto and envelope |
| Nulls/interventions | 128 Haar bases per observer/state/rank; each of four causal arms with per-state norm-matched random; T1 3-arm screen plus mandatory readout ablation | measured minimum cover and Chernoff allocation on new development rows |
| Decisions | six-seed paired comparisons, per-seed counts, raw rank p and Holm; task MSE, capability and unseen joint-intervention prediction | confirmation only after new protocol and split hashes, model/checkpoint source and separate unseal approval |

**No new ROC-02 training or headlines executed.** The source and registration exist on the public branch. The original NRF v0.4 paper is a retrospective analysis of previously exposed model folds.

## Public execution and evidence

- Source: research/observer_calculus/observer_card.py, nrf_retrofit.py, theory.py, frontier.py, closure_sweep.py.
- Data: ROC01_NRF11_PER_STATE_PARTIAL.csv (1,584 records), ROC01_NRF11_PER_SEED_DECOMP.csv, ROC01_NRF11_SUMMARY.json.
- Formal code: MathCan/ObserverReportCard.lean and MathCan/ObserverChernoff.lean.
- Registration and dated amendment: ROC01_REGISTRATION.md, ROC01_AMENDMENT_2026-11-16B.md, PART4_NEXT_REGISTRATION.md.
- [Successful ROC Python/Lean run](https://github.com/patrickdugan/MathCan/actions/runs/43798677237) after null/Lean corrections: 29 ROC Python tests, five inherited NRF receipt tests, kernel-checked finite lemmas. The original failed intermediate runs remain visible.
- Full neural checkpoint replay and genuine ROC rank-k statistical inference are pending independent model and adapter bytes.

This document is the Fable-facing review surface. Source and rows are present in public MathCan; anything absent remains explicitly unverified.
