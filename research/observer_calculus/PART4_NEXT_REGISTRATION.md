# ROC-02: prospectively registered delayed-rule carry observer experiment

**Frozen before any new task sample or neural training:** 2026-11-16.
This file is Part 4 of ROC-01. It defines the next independent experiment; it
is not evidence that a model has already learned the task or that a low-rank
mechanism has been discovered. Amendments must be dated and preserve this text.

| Dimension | Frozen specification | Acceptance/reporting |
|---|---|---|
| Task | **Delayed-rule binding with distractor rewrites**: a sequence introduces one of eight input/output rules, supplies optional distractor bindings, then requests a mapped output only after a variable 2–16-step delay; use a separate exact symbolic interpreter | All labels and collision/failure states verified independently; explicit no-rule/out-of-domain cases; monitor visible cue and hidden rule-state |
| Model | Recurrent tied residual MLP, state d=128, parameter-shared transition, recurrent training depths 8/16, task-readout eight labels; six model initialization seeds 2026111601, 2026111603, 2026111607, 2026111609, 2026111613, 2026111619 | Fixed capacity/optimizer exposure, raw model metrics, source/checkpoint hash before fitting any observer |
| Generator | train seed 2026111621, calibration seed 2026111623, sealed test seed 2026111627; 1024/256/384 distinct structured records, disjoint by **rule family + source composition** | Split hash and exact-rule overlap audit. Model validation cannot see sealed output labels until all observer fits, selected ranks/penalties and null definitions frozen |
| Observer rank | **k in {2,4,8,12,16,32}**, U orthonormal; 32 purely prospective control; train-only SVD, supervised task-only, OLM-07 Gramian top-k, and leakage-penalized candidate | Compare each fitted basis against equal-budget task-only with exactly same starting U, 80 optimizer steps, Adam lr 0.02, QR every step; no fit on test |
| Outputs | Predict true rule answer, optional next-state/carry readout and 8-dimensional task logits; at n in {1,2,4,8,16} future recurrences | Report raw task MSE, accuracy, source error, certified causal output Gram H per declared output/horizon; state-by-state ROC card a,b,c,s,task MSE |
| T-C identification | Minimal **three** source intervention types under the synthetic table from Part 2: dark→observed, observed→dark, freeze U; always include the fourth ablate-U-at-readout arm as a falsification control | Must recompute actual BPD-01 T1 cover from observed dev effect distributions; allow no separating set or 'none fits'. Chernoff allocations use dev data only |
| Random baselines | For each (seed,rank,observer,state), **128 rank-k random orthonormal bases** keyed by seeds 941001..941128, a separate norm-matched random intervention for every active causal arm, and an input-level rule/cue augmentation comparator | One-sided add-one rank p, 5-family Holm adjustment, per model paired seed changes and k/6 counts, null failures retained. Reject mismatched initial norm/readout route |
| Objective / tradeoff | J=task MSE + lambda * (||B||F/||D||F)^2; evaluation anchor lambda=1.0, exploratory lambda grid {0,0.05,0.2,1,2}. Report full exact lower envelope | Per-seed floor and switch points; 3D nondominated (k,error,normalized||B||) surface including unsupported candidates and cost of rank |
| Intervention radius | Base r=0.2 in hidden-state physical L2, independent seed-tagged donor/random draws, radius ladder {0.05,0.1,0.2} on **calibration only** | Compare next output and 2/4/8/16-step effects; invalid readout or radius matching reported as invalid, never silently dropped |
| Criterion | For each task/coupling endpoint, report six paired model values; a claim of learned causal differentiation needs a new family holdout and correct prediction of unseen pairwise joint-ablation effects | Candidate must exceed best of input augmentation, task-only and random-basis interventions on the registered test; 5/6 seeds directionally consistent, Holm-adjusted p<=0.05 when rank statistics support it. The known exact symbolic interpreter remains a strong baseline |
| Resources | CPU and local accelerators, no paid compute by default, no large model claim; source model and per-state Jacobian checkpoint files are required before opening test | Emit reproducible per-state CSV and standalone script to public MathCan at a pinned SHA. Checkpoint blobs and declared output/J evidence must be verifiable by an independent reviewer |

### Identifiability safeguard

A scalar rank-one observer can separate any finite corpus using arbitrary
precision. Therefore a successful finite quiz alone is not a rank floor.
ROC-02 must measure the **linear decoder rank**, the **fixed precision/margin
budget**, and the **closure residual B** separately. Classification tags
remain nonexclusive and local. Predictions of extra-loop behavior require a
specified state-visit and output-time contract.

A strong mechanistic positive needs evidence that interventions on the hidden
state convey information absent from an equal-cost input intervention,
including appropriate source-vs-carried-state conflict tests. The historical
NRF v0.4 tradeoff is **retrospective** and cannot determine the new test
lambda or ranking winner.

### Claim and publication gate

No sampling, model fitting, checkpoint action, or new headline experiment was
performed when this registration was committed. First verify Parts 0–2 in
MathCan, finish exact sources and Lean scope, identify an EvalMath scorer
capable of checking all case labels, then train and lock checkpoints. The
user must authorize paid resources separately. A clean negative result and
undefined causal Gram s are registered outcomes, not excluded cases.
