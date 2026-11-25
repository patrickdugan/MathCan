# Source-rule transfer, recurrent observer geometry, and counterfactual-gradient limits

**ROC-02–06 empirical paper update · version 0.5 · 25 November 2026**

*MoralityLabAI / MathCan research note. Experimental subject: 128-dimensional parameter-tied residual networks on an eight-class delayed rule-binding task, and a later query-conditioned table-memory model.*

## Abstract

Low-dimensional observers of recurrent hidden states are often selected by task reconstruction error, local Jacobian closure, and future-output sensitivity. ROC-02 tests whether suppressing dark-to-observed computed-change coupling gives an intervention-level advantage. Across twelve frozen depth-8/16 residual models, regularized rank-7/8 observers improve calibration MSE and rank-matched null-normalized coupling over equal-budget task-only observers in all 24 model-rank comparisons. A registered input-grounded rule-edit intervention, ROC-02E, then yields a mean original-logit target-margin gain of only +0.00014148 relative to task-only at depth 16/rank 7, with three of six positive seeds and a one-sided exact sign-flip p-value of 0.375. The original model's delayed-rule calibration accuracy is around 22%, which limits the interpretation of its future-logit Jacobian.

ROC-03A and ROC-03B expose task-learning limitations: increased training of the original recurrent model leaves large training errors, while a query-conditioned table decoder reaches perfect training accuracy on four affine rule families yet reconstructs zero complete tables on 256 different calibration-family cases. ROC-04A directly varies rule diversity at fixed model architecture, example count, optimizer exposure, initialization and schedule. On a new exposed set of 256 unseen permutation tables, six matched seeds trained with 512 distinct tables improve mean queried-answer accuracy from **22.92% to 70.70%**, a **+47.79 percentage-point** gain (6/6 positive seed differences; one-sided sign-flip **p=0.015625**). The preregistered primary transfer gate passes. The separate competence gate fails: complete eight-row table recovery averages **11.13%**, with 0/6 seeds meeting its 50% requirement. Legal rule-table edits elicit 73.76% mean changed-answer accuracy; label-preserving distractor edits retain predictions on 92.53% of eligible cases.

ROC-04B then evaluates the **same twelve frozen checkpoints** on 384 previously reserved, disjoint rule permutations, generated after a separate preregistration. The higher-diversity arm attains **73.05%** test accuracy and the four-rule arm **21.09%**, for a **+51.95 percentage-point** paired six-seed gain (6/6 positive seeds, exact one-sided p=0.015625). The registered reserved-set primary gate passes. The separate competence gate fails again: complete eight-row reconstruction averages **11.89%**, and zero of six models reach 50% complete-table accuracy. ROC-04B includes a documented pre-result correction of one truncated checkpoint hash and subsequent full replay. The original ROC-02 sealed source families 6–7 remain unopened. Independent rule-identity confirmation strengthens the training-distribution effect while leaving full symbolic table recovery and low-rank causal-mechanism identification unresolved.

ROC-05A adds **six fresh model initializations** and independent training and development permutation pools, excluding all 1,152 ROC-04 train/development/consumed-test table identities. At fixed architecture and optimization, the 512-rule arm scores **74.67%** on 256 new exposed development permutations versus **20.51%** for the four-rule arm, a mean **+54.17 percentage-point** advantage (6/6 positive model seeds, one-sided exact sign-flip p=0.015625). The independent-seed primary replication gate passes, while complete all-eight-row table recovery averages **13.41%** and its competence gate fails. A second CPU training replay confirms the primary direction with +54.62 percentage points, although just 2/12 checkpoint files are byte-identical across runners; the original first-run weights are retained for mechanistic testing.

With those exact first-run weights frozen, ROC-05B tests a supervised train-only rank-7 observer on the recurrent hidden state after four of eight tied steps, using source-rule row swaps and same-physical-L2 input interpolation on the **already exposed** ROC-05 development cases. At radius 0.20, the mean target-margin gain is **+0.11797** for rank-7 observed rule steering and **+0.18602** for the equal-radius off-manifold softened input. The registered observer-minus-input contrast is **−0.0680534**, with **0/6** positive seed effects and one-sided exact p=1.0. All 73,728 intervention records pass independent audit; **0/48** null-calibrated local observer cards meet complete mechanism-tag predicates. A valid full discrete rule-table edit still yields **75.33%** new-answer accuracy in the high-diversity networks. The experiment bounds this chosen low-rank causal route while preserving the behavioral generalization benefit of source-rule diversity. The ROC-05 reserved 384-table identities remain without generated test examples, and the original ROC-02 sealed families 6–7 stay unopened.


ROC-06A extends the mechanistic question to a train-only **counterfactual-gradient rank-seven observer** on the twelve original frozen ROC-05A models. It improves native changed-target hidden-state steering from +0.117968 under the supervised rank-seven observer to **+0.129377** (6/6 seeds improve), while an equal-hidden-L2 off-manifold softened-input control yields **+0.186021**. The registered gradient-minus-best-reference contrast is **−0.05664404**, with 0/6 positive model seeds and exact one-sided sign-flip p=1.0. The training-gradient basis captures more future-logit Jacobian energy (31.51% versus 26.31%) yet does not lower incoming computed-change coupling below its matched random median. All 72 observer cards remain unclassified. The new analysis uses ROC-05's exposed development pool, leaving its 384 reserved future rule identities and the original ROC-02 family-6/7 tests unopened.


## 1. Research question and evidence sequence

A recurrent model evolves a hidden state through tied transformations. A rank-\(k\) observer reads only the coordinates along an orthonormal basis \(U\). The ROC-01 calculus separates what changes within that subspace from what enters it from its dark complement and what leaves it. A small incoming-coupling block is attractive as a closure diagnostic, especially when a low-rank readout still predicts the training objective.

The immediate empirical question is sharper: **Does the leakage-regularized observer react to an authentic change of the remembered source rule more usefully than an equally trained task observer or a same-dose input control?** The study uses already trained and frozen neural networks. Its primary endpoint is obtained from their original final logits after physically matched hidden-state interventions, rather than from a refitted observer head.

The evidence sequence has a dependency structure:

- **ROC-02:** fixed source generator and twelve 240-update model checkpoints, including SHA-256 source and weight receipts; train families 0–3, calibration families 4–5, unopened procedural holdout 6–7. [Source and training](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/roc02_delayed_rule_v1).
- **ROC-02B:** a preregistered nine-rank pilot with 128 SHA-keyed rank-matched null subspaces per state, 27,648 published null rows, and original future-logit Jacobian capture. All 432 observer-state cards remain unclassified under the complete ROC-01 Amendment C criteria. [Merged PR #124](https://github.com/MoralityLabAI/LoopedTransformers/pull/124).
- **ROC-02C:** equal-budget, 80-step optimization of rank-7 and rank-8 observers, with calibration-selected regularization. [Merged PR #144](https://github.com/MoralityLabAI/LoopedTransformers/pull/144).
- **ROC-02E:** physically controlled rule-versus-cue intervention using the newer ROC-02C observers, with 256 paired calibration records per model. [Merged PR #147](https://github.com/MoralityLabAI/LoopedTransformers/pull/147).
- **ROC-03A/03B:** stronger model training and an explicitly query-conditioned decoder, revealing severe overfitting to four affine rule tables. [Merged PRs #149](https://github.com/MoralityLabAI/LoopedTransformers/pull/149) and [#150](https://github.com/MoralityLabAI/LoopedTransformers/pull/150).
- **ROC-04A:** a registered six-seed comparison of four versus 512 training permutations at a matched optimization budget, tested on 256 exposed development rule identities. [Merged PR #155](https://github.com/MoralityLabAI/LoopedTransformers/pull/155).
- **ROC-04B:** the same twelve frozen checkpoints scored once under the successful hosted confirmation protocol on 384 previously reserved rule identities, with a full per-case independent receipt audit. [Merged PR #157](https://github.com/MoralityLabAI/LoopedTransformers/pull/157).
- **ROC-05A:** a fresh six-model-seed replication with new train and exposed development rule-table identities excluding every ROC-04 training/development/consumed-test permutation. Both training arms retain the same budget. [Merged PR #162](https://github.com/MoralityLabAI/LoopedTransformers/pull/162).
- **ROC-05B:** the original twelve ROC-05A first-run models frozen to exact checkpoint hashes; matched physical source-input and rank-seven hidden interventions on ROC-05 development cases, with complete local ROC-01 null cards. [Merged PR #163](https://github.com/MoralityLabAI/LoopedTransformers/pull/163).

The earlier ROC-02C [PR #127](https://github.com/MoralityLabAI/LoopedTransformers/pull/127) and ROC-02D [PR #130](https://github.com/MoralityLabAI/LoopedTransformers/pull/130) form a distinct pilot lineage, using rank-eight adapters selected with a different gamma grid. Their observed 11/12 lower source-change readout sensitivity is relevant prior calibration evidence; it is never pooled with the newer rank-7/8 observers.

## 2. Observer geometry and training objective

Let \(F_{\mathrm{suffix}}\) be the remaining recurrent updates from the chosen midpoint state \(h_i\), and write

\[
T_i = D F_{\mathrm{suffix}}(h_i),\quad D_i = T_i-I,\quad P=UU^{\mathsf T}.
\]

For an orthonormal \(U\in\mathbb R^{128\times k}\), the incoming computed-change block is \(B_i=U^{\mathsf T}D_i(I-P)\). Its scale-free size and its rank-conditional null-normalized square are

\[
b_i(U)=\frac{\lVert B_i\rVert_F}{\lVert D_i\rVert_F},
\qquad \ell_i(U)=\left[\frac{b_i(U)}{m_{b,i}(k)}\right]^2.
\]

Here \(m_{b,i}(k)\) is the median of exactly 128 SHA-keyed Gaussian/QR rank-\(k\) random subspace measurements on the same model and state, and is held fixed during optimization. Undefined denominators cause abstention. The original trained model's future-logit sensitivity Gram is \(H_i=(R T_i)^{\mathsf T}(R T_i)\) for its frozen eight-logit readout \(R\); the reported capture is \(s_i(U)=\mathrm{tr}(U^{\mathsf T}H_iU)/\mathrm{tr}(H_i)\), when the denominator is positive.

Each observer starts from the same train-only supervised cross-covariance basis and receives 80 Adam updates at learning rate 0.02, with QR retraction and a refitted train-only ridge head. The comparator sets \(\gamma=0\). Joint candidates use \(\gamma\in\{0.05,0.2,1.0\}\) in \(\mathrm{MSE}_{\mathrm{train}}+\gamma\operatorname{mean}_{i=0,1}\ell_i\). Candidate selection uses calibration cases and two additional calibration shadow states, requires calibration task MSE at most 1.10 times the equal-budget task-only MSE, and minimizes the \(\lambda=1\) reference objective. Additional shadow states remain within the same calibration source families. The selected gamma therefore has **selection optimism**, even though the grid and selection rule were precommitted.

The original neural models have 128 hidden dimensions, a 79-feature event encoder, and tied tanh residual updates at depths 8 or 16. Their pre-observer mean calibration accuracies are 0.215495 and 0.223958, respectively. Output-Gram capture in this model population measures sensitivity of weak trained logits, which can differ from the correct delayed-rule answer.

## 3. ROC-02C calibration measurements

Means below aggregate the six seeds within each depth and rank. MSE is the same exposed family-4/5 one-hot ridge prediction error used to select gamma. The coupling metric is \(\operatorname{mean}\ell_i\) on the selected calibration shadow states. These quantities are descriptive.

| Depth | Rank | Task-only MSE | Joint MSE | Task-only \(B^2/\mathrm{null}^2\) | Joint \(B^2/\mathrm{null}^2\) | Task-only \(H\) capture | Joint \(H\) capture |
|---|---:|---:|---:|---:|---:|---:|---:|
| 8 | 7 | 0.1055 | 0.0972 | 2.466 | 0.0238 | 0.397 | 0.630 |
| 8 | 8 | 0.1059 | 0.0979 | 1.776 | 0.0226 | 0.367 | 0.632 |
| 16 | 7 | 0.1058 | 0.0976 | 2.783 | 0.0385 | 0.348 | 0.842 |
| 16 | 8 | 0.1067 | 0.0981 | 2.583 | 0.0346 | 0.394 | 0.846 |

All 24 model-rank cells improve both the exposed calibration MSE and the null-normalized squared incoming-coupling score relative to their equal-budget task-only twin. The depth-16, rank-7 normalized coupling drops by approximately 98.6% of the task-only value. The frozen original logits themselves are independent of which observer basis is being compared.

The ROC-02B rank sweep had already found zero fully classified ROC-01 mechanism cards, even where individual coupling and future-logit capture tails were notable. ROC-02C improves an *observer fitting objective*, leaving the causal rule-binding hypothesis to an intervention.

## 4. ROC-02E causal contrast

The calibration rule family 4 maps \(q\mapsto(3q+1)\bmod8\), and family 5 maps \(q\mapsto(3q+5)\bmod8\). For each of 256 calibration records, create two distinct valid counterfactuals:

1. **Early rule edit:** replace only the original source-A binding table by the other calibration-family table.
2. **Late cue edit:** replace only the final query index \(q\) with \((q+4)\bmod8\).

Both exact symbolic counterfactuals have the same new target \(y'=(y+4)\bmod8\), and every intermediate event and distractor is preserved. The discrete edits have different encoded input \(L_2\) norms (4 and \(\sqrt2\)). Their full-input effects retain those natural costs and are reported separately.

For the matched controls, interpolate each source edit along the encoded feature path until its induced midpoint hidden shift reaches a registered radius \(r\in\{0.05,0.10,0.20\}\). These intermediate feature vectors are off the legal discrete input manifold. On the same original midpoint, inject the legal edit's induced hidden difference into the rank-\(k\) observer span, into its dark complement, or along the full input-induced direction, scaled to the same radius. Random observer-span and isotropic controls are SHA-keyed; each uses the same suffix and frozen original readout.

For original logits \(z\) and post-intervention logits \(z'\), with original correct class \(y\), define the target margin gain

\[
g = [z'_{y'}-z'_y]-[z_{y'}-z_y].
\]

The preregistered primary analysis compares the mean \(g\) under **early-rule-induced observed-subspace steering**, for joint and task-only observers at depth 16, rank 7, and hidden midpoint radius 0.20. Within each model, average over all 256 paired dev records. The six independently initialized models form the inference units.

The complete experiment produced 516,096 effect records across twelve models: \(256\times2\) edit kinds \(\times2\) ranks \(\times2\) observer fits \(\times3\) radii \(\times7\) routes \(\times12\) frozen models. SHA-verified source/weight files and the exact prescribed observer replay guard the provenance; cross-run CPU QR/BLAS floating-point drift is separately recorded under an explicit numerical tolerance.

## 5. Registered primary result

| Depth-16, rank-7, radius-0.20 quantity | Observed mean |
|---|---:|
| Task-only rule-induced observed steering gain | +0.001606 |
| Joint rule-induced observed steering gain | +0.001748 |
| Joint minus task-only | **+0.000141483** |
| Positive paired seed differences | **3/6** |
| One-sided exact sign-flip p, 64 sign allocations | **0.375** |
| Descriptive six-seed t interval, 95% | **[−0.001011, +0.001294]** |

The six preregistered paired effects, indexed by original initialization seed, are:

| Seed | Joint minus task-only target-margin gain |
|---|---:|
| 2026111601 | +0.001742165 |
| 2026111603 | −0.001148760 |
| 2026111607 | −0.000597024 |
| 2026111609 | −0.000604106 |
| 2026111613 | +0.000659989 |
| 2026111619 | +0.000796637 |

For a fixed six-vector of seed effects \(d_s\), enumerate all \(2^6=64\) independent sign flips and compute the fraction whose mean is at least the observed mean. This yields \(p=0.375\) for the one-sided direction. Since gamma was chosen using the same calibration source families as this causal follow-up, this exact calculation is **descriptive** and is not a prospective source-family generalization p-value. No independence is attributed to the 256 cases within any one model seed.

The registered primary differentiation criterion fails. At the same depth/rank/radius, mean early-rule soft-input gain is +0.001036, and late-cue soft-input gain is −0.000293. Their output effects cannot be treated as semantic success for the off-manifold interpolated inputs. Full legal early-rule input changes produce +0.012010 mean target-margin gain at their natural, larger hidden dose. A post-hoc per-case maximum over several control routes exceeds joint observed-rule steering by 0.016509 on average, with 0/6 seeds beating that oracle upper envelope; this is a **descriptive, hindsight-selected ceiling**, not a usable fixed comparator.

The older ROC-02D pilot reported reduced source-binding readout sensitivity in 11/12 seed/depth cells from its different rank-eight/gamma-through-2 observer lineage. Its six-case calibration sample and different endpoint prevent statistical pooling with ROC-02E.

## 6. Interpretation

The observed success of the rank-null-normalized coupling objective can coexist with an absent or weak source-rule effect. A rank-\(k\) subspace may capture large local sensitivity directions of the original future logits while those logits solve the delayed-rule task poorly. Suppressing incoming computed-change coupling also permits the observer to allocate capacity to stable, task-decoding features whose response to a legal input counterfactual is limited. The experiment directly tests one such observer-based steering route; it does not establish that every low-leakage observer erases task information, nor does it characterize all possible causal interventions.

The source-rule and late-cue edits share the exact new target, which controls target identity. Their physical geometry differs, and only the continuous-input controls enforce equality of hidden midpoint dose. This distinction matters when attributing differences to carried rule memory instead of input magnitude or output orientation.

The current evidence favors a more careful claim: **On twelve weak short-trained synthetic recurrent models, leakage regularization consistently improved exposed calibration reconstruction and null-relative coupling, while its registered rule-specific physical intervention showed no consistent paired six-seed improvement.**

## 7. Limits and next experiment

The original models have low calibration accuracy, only six independent initialization seeds per depth, and eight-class synthetic data. ROC-02C's gamma selection reuses the calibration labels. ROC-02E's causal results reuse those exposed families. The originally registered nine-rank ROC-01 observer report is incomplete, and causal mechanism identification with measured Chernoff allocation remains pending. The legal label-preserving distractor intervention and a fresh source-family holdout are separate scientific gates. The sealed families 6 and 7 were neither read nor used to tune this study.

The later ROC-03 and ROC-04 cohorts investigate model competence and source-rule diversity under separately frozen protocols, as documented in the dated postscript sections. A deterministic symbolic table interpreter solves these generated tasks by construction, providing an exact reference for the still-incomplete neural solution. The next mechanistic gate requires independently confirmed rule competence, matched input-level causal comparators, complete rank-matched null cards, and a frozen six-seed inference plan.

## Dated postscript: ROC-03A training-competence gate (17 November 2026)

Following the negative ROC-02E rule-intervention result, a separate source-locked feasibility experiment [ROC-03A, merged LoopedTransformers PR #149](https://github.com/MoralityLabAI/LoopedTransformers/pull/149) tested whether greater optimizer exposure could make the **original architecture** learn its task reliably. The protocol was committed at `39ef4b657edca1b77ada9be745cc71f57e0776b2` before the new fit. One fresh initialization, `2026111701`, used the original depth-8, width-128 tied residual model, 1,920 AdamW updates, batch size 32, and the same SHA-verified train (families 0–3) and exposed calibration (families 4–5) files. The final training checkpoint was selected at the precommitted update count, regardless of calibration accuracy.

| ROC-03A fixed update | Training accuracy /1,024 | Calibration accuracy /256 |
|---:|---:|---:|
| 240 | 296/1,024 (28.91%) | 54/256 (21.09%) |
| 480 | 338/1,024 (33.01%) | 66/256 (25.78%) |
| 960 | 330/1,024 (32.23%) | 58/256 (22.66%) |
| 1,920 | **362/1,024 (35.35%)** | **72/256 (28.13%)** |

The preregistered competence gate required 90% training accuracy and 70% calibration accuracy at the final update. **Both thresholds failed.** The final training and calibration cross-entropies were 1.344957 and 1.394293, respectively. Independently reloading the 1,920-step model reconstructed these scores and the checkpoint SHA-256 `bac422572c6bac3dbeca11f3f49feed4a25d61742855a6e8690186f0c088be3d`. A hosted CPU workflow reproduced the original checkpoint hash **byte for byte**. The original depth-8 ROC-02 six-seed model mean was 24.15% train and 21.55% calibration, using a different initialization set and shorter training, so the numerical improvement is a descriptive cross-cohort contrast.

The longer-training model remains weak on **its own training data**. This places an additional constraint on interpreting ROC-02E's causal null: source-rule competence is already missing upstream of the observer fitting problem. ROC-03A contains only one fresh seed, and neither its training change nor its calibration outcomes establish independent-family generalization. The sealed source families 6–7 remain unopened. A subsequent dated protocol should test a learnable query-conditioned binding retrieval architecture alongside a matched original-architecture control, with an explicit task-competence gate before assigning any mechanism label.

## Dated postscript: ROC-03B identifies unseen-table memorization (17 November 2026)

A second, separately preregistered training pilot, [ROC-03B LoopedTransformers PR #150](https://github.com/MoralityLabAI/LoopedTransformers/pull/150), addressed ROC-03A's weak training fit by supplying an explicit final-query route to the readout. A 128D tied recurrent state processes the early A binding and intervening distractor/carry events; a learned decoder predicts 8×8 table-row logits from that state, and the final visible query one-hot chooses the requested row. The route is a designed inductive bias. The protocol at `750e6a9e14fb5116082bb0ffdf967ed173e69e94` fixed two identical-start 1,920-step arms: task-only, and task loss plus 0.5 times eight-row A-table reconstruction loss from training inputs. Both see exactly the same original training families 0–3. Family-4/5 calibration labels remain outside gradient fitting.

| ROC-03B 1,920-step arm | Train answer accuracy | Calibration answer accuracy | Train full-table accuracy | Calibration full-table accuracy |
|---|---:|---:|---:|---:|
| Task-only query-conditioned | 100% | **78/256 (30.47%)** | 100% | **0/256** |
| With eight-row table supervision | 100% | **74/256 (28.91%)** | 100% | **0/256** |

The table-supervised arm's calibration rowwise accuracy is 25.59%, with calibration cross-entropy **11.5879**. The fixed train ≥90% and calibration ≥70% task-competence gate **fails**. Both trained checkpoints and all eight milestones were independently replayed in [hosted CPU CI](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44069373243).

A **post-hoc** diagnostic of the published calibration predictions identifies the learned restriction: the decoded complete table exactly equals one of the four *training-family* rule tables on **244 of 256** calibration cases in the table-supervised arm (216/256 task-only). The true calibration tables belong to different source families, and the model decodes only six distinct table vectors under table supervision. This check was conducted after the registered outcome, on the already exposed calibration families. It is an observational output diagnosis, with no new-source inferential status.

Together the two follow-ups separate failure modes: the original linear-readout recurrent model struggles even on its training examples after longer optimization, while the query-conditioned table decoder fits those four training rule families perfectly and fails to transfer to the original calibration tables. ROC-04A then tests the role of combinatorial training-rule support with a newly frozen, disjoint permutation pool and equal-budget controls. Families 6 and 7 from the original ROC-02 sealed test remain unopened.

## Dated postscript: ROC-04A permutation diversity and unseen-development transfer (17 November 2026)

The ROC-03B results prompted a separately preregistered study of rule-distribution support. [ROC-04A, merged LoopedTransformers PR #155](https://github.com/MoralityLabAI/LoopedTransformers/pull/155), froze its source and training protocol at commit `5dbf46e428e495b36d3d50470197540ca39a9a4e` before generating new source examples or fitting the models. The comparison fixes the depth-eight, width-128 `QueryConditionedTableMemory` model with **51,520 parameters** and an explicitly supplied final-query-to-table-row route. Two arms receive identical initial weights within each of six fresh seeds, the same 1,024 event schedules and minibatch index streams, batch size 32, 1,920 AdamW updates at learning rate 0.001, and task cross-entropy plus 0.5 times all-eight-row table reconstruction cross-entropy. The active source-A binding table and its answer label are the training factors that differ.

The **low-four** arm uses the four original ROC-02 training-family affine rules, with 256 examples of each. The **high-512** arm uses 512 separately sampled permutation tables, two cases per table. Its 512 source identities were drawn from the 40,320 bijections of eight values after excluding all eight original ROC-02 affine tables. A disjoint development set contains **256 new rule tables, one case per rule**. Another **384 table identities** were assigned to a separately reserved test split, for which no examples or labels were generated during ROC-04A. The generator checks every target against the exact symbolic interpreter and literal table-row lookup; event schedules, distractors and queries are matched between training arms. The original ROC-02 sealed source families 6–7 remain untouched.

### Frozen primary comparison and six-seed results

At the fixed last update, the primary endpoint is the within-seed difference in correct queried answers on those same 256 development permutations. The preregistered gate requires at least five positive seed differences, a mean accuracy gain of at least 20 percentage points, and a one-sided six-seed exact sign-flip p-value at most 0.05.

| Seed | Four-rule accuracy | 512-rule accuracy | Gain | High-512 full-table exact |
|---|---:|---:|---:|---:|
| 2026111705 | 58/256 (22.66%) | 182/256 (71.09%) | +48.44 pp | 39/256 (15.23%) |
| 2026111707 | 58/256 (22.66%) | 183/256 (71.48%) | +48.83 pp | 25/256 (9.77%) |
| 2026111711 | 61/256 (23.83%) | 153/256 (59.77%) | +35.94 pp | 13/256 (5.08%) |
| 2026111713 | 62/256 (24.22%) | 193/256 (75.39%) | +51.17 pp | 26/256 (10.16%) |
| 2026111717 | 61/256 (23.83%) | 198/256 (77.34%) | +53.52 pp | 42/256 (16.41%) |
| 2026111719 | 52/256 (20.31%) | 177/256 (69.14%) | +48.83 pp | 26/256 (10.16%) |
| **Mean** | **352/1,536 (22.92%)** | **1,086/1,536 (70.70%)** | **+47.79 pp** | **171/1,536 (11.13%)** |

The exact mean six-seed improvement is **734/1,536 = 0.4778645833**. All **6/6 seeds** favor greater rule diversity. Enumerating the 64 sign assignments of the *six paired seed-level differences* yields one assignment at least as extreme in the registered positive direction: **p=1/64=0.015625**. **The primary ROC-04A gate passes.** The 256 examples per seed share the same exposed development-rule pool, so this sign-flip calculation describes variation across model initializations conditional on that pool; it provides no independent reserved-set outcome.

The **separate competence gate fails**. It required at least five seeds to reach both 70% queried-answer accuracy and 50% exact recovery of *all eight table rows*. Only **4/6** high-diversity models reach the first threshold; **0/6** reach the second. Mean development rowwise reconstruction is **74.10%**, with mean complete-table recovery only **11.13%**. Greater permutation exposure improves queried-answer generalization substantially while leaving a faithful complete-table representation largely unverified.

### Post-training legal edits and causal interpretation

After the fixed checkpoint, the experiment swaps two values in the initial source-A binding table, at query row `q` and row `(q+4) mod 8`, preserving the query and intermediate events. The exact symbolic target changes. The high-512 arm answers this legal edited rule correctly on **73.76%** of development cases, averaged over six seeds, while low-four answers **23.96%**. Among the **221/256** examples with an eligible B/C distractor event, an unrelated distractor-table replacement preserves the true answer; high-512 predictions remain invariant on **92.53%** of eligible cases on average. These task-level edits have their natural input and hidden-space costs and have not been matched to ROC-01's physical intervention radius.

The four-rule arm's new development accuracy of 22.92% and ROC-03B's original calibration accuracy of 28.91% are outcomes on **different development distributions**; those cross-study figures are contextual. ROC-04A's positive inference comes from the *within-study* 4-versus-512 source-diversity comparison, with identical development inputs and paired model seeds. The model receives explicit lookup-table bits and a designed query-to-row readout; the study supports generalized queried-answer behavior under increased permutation diversity, without identifying an emergent exact dynamical quotient or proving recurrent storage of every rule-table row. The symbolic oracle remains correct by construction on all valid examples.

The [hosted six-seed replay](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44085250022) passed the independent source checks, twelve frozen model/optimizer checkpoint receipts, and original-versus-edited per-case audit. The full archived data comprise **44 SHA-256-indexed files**, including all twelve 1,920-step model checkpoints, the generated train/development source files, and the six-seed summary. The standalone archive has SHA-256 `e16cfca1feae0a495cf86a93a2ff669ab1c699c1b61a6d550a68c2f7de5e12e6`; the original [six-seed source CSV](https://github.com/MoralityLabAI/LoopedTransformers/blob/main/experiments/roc04_permutation_transfer/ROC04A_PRIMARY_BY_SEED.csv) is reproduced byte-identically in this paper directory. An additional standard-library verifier at `papers/roc02/roc04a_primary_signflip_v01.py` checks all integer counts, thresholds, exact p-value, and CSV's original Git blob.

### Next confirmatory boundary

At the time of ROC-04A publication, the separate **384-table reserved evaluation** still awaited a frozen ROC-04B confirmation protocol and the release of new source examples. ROC-04B has now completed that evaluation under the registered model and source lock, as documented in the following dated postscript. ROC-01's low-rank A/B/C/H closure classification and equal-dose causal control program remain further experiments. The original ROC-02 sealed families 6–7 constitute a distinct procedural holdout and remain unopened.

## Dated postscript: ROC-04B prospectively reserved permutation confirmation (17 November 2026)

After ROC-04A's positive exposed-development transfer result, a separate [ROC-04B preregistration](https://github.com/MoralityLabAI/LoopedTransformers/pull/157) froze the evaluation of **384 additional permutation-table identities**, allocated in ROC-04A's deterministic source pool before the twelve models were trained. The protocol at commit `f032c52db2ebb544b745b3972f5f86f4c47c8b38` fixed the original twelve ROC-04A step-1,920 checkpoint digests, the new test schedule seed `20261117101`, both primary and competence criteria, and exact one-sided sign-flip inference before constructing the new source examples or labels.

ROC-04B tests the same depth-eight, 51,520-parameter query-conditioned recurrent model trained either on four repeated affine source rules or 512 distinct permutation rules. Across the six original paired initialization seeds, each arm receives **the same 384 previously reserved table identities**, one newly generated delayed-rule case per table. These tables are disjoint from the 512 high-diversity training rules, the 256 exposed ROC-04A development rules, and the eight prior ROC-02 affine rules. A separate generator seed creates new event schedules. The direct table-row lookup and symbolic source-binding interpreter agree on all 384 labels. The models remain fixed at their frozen last training step, with **zero new training updates** or checkpoint reselection.

### Primary reserved-test result

| Fixed model seed | Four-rule correct /384 | 512-rule correct /384 | High − low | High exact complete table /384 |
|---|---:|---:|---:|---:|
| 2026111705 | 76 (19.79%) | 296 (77.08%) | +57.29 pp | 79 (20.57%) |
| 2026111707 | 75 (19.53%) | 265 (69.01%) | +49.48 pp | 38 (9.90%) |
| 2026111711 | 83 (21.61%) | 272 (70.83%) | +49.22 pp | 29 (7.55%) |
| 2026111713 | 85 (22.14%) | 295 (76.82%) | +54.69 pp | 55 (14.32%) |
| 2026111717 | 82 (21.35%) | 291 (75.78%) | +54.43 pp | 51 (13.28%) |
| 2026111719 | 85 (22.14%) | 264 (68.75%) | +46.61 pp | 22 (5.73%) |
| **Six-seed mean** | **486/2,304 (21.09%)** | **1,683/2,304 (73.05%)** | **+51.95 pp** | **274/2,304 (11.89%)** |

The exact six-seed mean paired accuracy improvement is **1,197/2,304 = 0.51953125**. The signed effect is positive in **6/6** frozen model seeds. Enumerating the 64 possible signs of the six paired seed-level differences yields one assignment at least as extreme as the observed improvement: **one-sided exact sign-flip p=1/64=0.015625**. The registered primary gate required at least five positive seeds, at least 0.20 absolute mean accuracy improvement, and p≤0.05; **all three conditions passed**.

The separate ROC-04B competence gate **failed**. Only **4/6** high-diversity models reach 70% test queried-answer accuracy, and **0/6** recover complete eight-row tables correctly on at least half of the cases. Their mean full-table accuracy is 11.89%, even though mean queried-answer accuracy reaches 73.05%. A deterministic direct-row lookup from the supplied source table remains correct on all valid inputs, which gives a precise oracle reference for residual model error.

The independent test is a holdout over source-table identities and schedules for **the same twelve trained model checkpoints**. The six paired model initializations remain the inference unit. ROC-04A and ROC-04B are statistically related through shared model weights and architecture, so their p-values cannot be combined as independent model-cohort replications. A future replication with newly trained model seeds and a newly frozen table pool could test that broader stability.

### Legal counterfactuals and nuisance specificity

Each reserved example receives a legal source-A binding-table edit that swaps its values at queried row `q` and `(q+4) mod 8`. The query, distractors and timing remain fixed, while the symbolic correct target changes. Frozen high-diversity models predict the new target correctly in **73.05%** of these edited-rule cases, averaged over six seeds; the low-four comparator reaches **22.22%**. Among examples containing a B/C distractor, changing an unrelated distractor table preserves the source-A answer. Under this label-preserving edit, high-diversity models retain their original prediction **93.55%** of the time on average, while low-four models retain **51.12%**.

These checks support behavioral dependence on the carried binding under legal discrete edits, with an explicit final query-to-row routing inductive bias. The edits have natural source and hidden-state costs. They are not a physical L2-matched low-rank Jacobian intervention, and they establish no ROC-01 five-mechanism identification or exact dynamical-quotient theorem.

### Provenance repair and independent reproduction

The initial preregistration accidentally stored a 40-character prefix in place of the full SHA-256 of the seed-`2026111719` `low_affine4` checkpoint. The first hosted attempt ([run #44087398369](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44087398369)) generated the reserved inputs and evaluated earlier models in memory, then stopped at the final checkpoint-hash check before publishing an aggregate result. The documented amendment at `2624b30a72ba5b500684067ff0f186906062e2e3` inserted the complete digest copied from the **unchanged ROC-04A checkpoint bytes and original manifest**. A preflight check of every checkpoint was added at `1fff17e286308550abc50f5235735bf249673527`, ahead of any reserved-test generation. This correction altered the provenance assertion alone, with the models, source seed, decision thresholds and all endpoint definitions held constant. Reporting the first attempt preserves the sequence of test access.

The successful [hosted ROC-04B confirmation run #44087829448](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44087829448) passed its independent standard-library audit of the exact 384 input/oracle pairs, all **4,608** model-case outcome rows, paired seed effects, and all 64 sign flips. Its complete archive includes the SHA-pinned original ROC-04A twelve-model reproduction ZIP, the new test source, per-case predictions and controls, preregistration, and a 16-entry file manifest. The standalone ROC-04B archive SHA-256 is `4d6539560fba91bffe083e77bb219d01823382cef9b1cd72e44c20595920520a`; the new source JSONL SHA-256 is `95614846bfac6fb66cdcf8c927cdf4a975ba92960dd6a2924ea344228dfef143`.

The [merged ROC-04B PR #157](https://github.com/MoralityLabAI/LoopedTransformers/pull/157) retains the frozen protocol, source/checkpoint hash correction history, complete six-seed result and executable independent audit. The raw original per-seed test CSV is copied **byte-identically** into this paper directory as `ROC04B_reserved_test_by_seed_v01.csv`. Its independent standard-library verifier `roc04b_reserved_signflip_v01.py` checks the original Git blob, all integer counts, the 64 sign flips and both gates.

ROC-04B establishes confirmatory transfer to reserved permutation identities for this frozen architecture and model cohort. The remaining scientific task is to test mechanistic structure on models that solve more of their delayed-rule task, using newly registered observer ranks, physically matched source-versus-hidden interventions, and ROC-01 Amendment C's full null and multiple-testing protocol. The original ROC-02 source families 6–7 remain unopened as an independent historical holdout.

## Dated postscript: ROC-05A fresh-seed replication and ROC-05B matched causal audit (17 November 2026)

### ROC-05A: fresh-source and model-seed rule-transfer replication

[ROC-05A, merged LoopedTransformers PR #162](https://github.com/MoralityLabAI/LoopedTransformers/pull/162), preregistered at commit a56c177bbc956274fbf65018b5724d291e25ef3c, repeated the four-rule versus 512-rule training experiment. The new high-diversity table universe excludes the eight original ROC-02 affine rules and all **1,152** identities previously allocated to ROC-04 training, development, and its now-consumed reserved test. A fresh deterministic permutation shuffle allocates 512 high-training tables, 256 different exposed-development tables, and 384 further reserved identities whose input examples and labels remain ungenerated.

The two training arms each receive 1,024 examples on the same train event schedules and final queries. Only the initial binding table and exact answer differ. Six **new independent initialization seeds** 20261117231, 20261117233, 20261117239, 20261117241, 20261117251, and 20261117257 train the same 51,520-parameter depth-eight query-conditioned model. Within each paired seed the original parameters, sampled minibatch index stream, 1,920 AdamW updates, task loss and 0.5 weighted eight-row table loss are matched. No dev-selected checkpoint or additional training is used.

The first complete six-model-seed hosted run supplies the **canonical outcome**:

| Original ROC-05 seed | Four-rule correct /256 | 512-rule correct /256 | High-minus-low gain | High full eight-row exact /256 |
|---|---:|---:|---:|---:|
| 20261117231 | 47 (18.36%) | 189 (73.83%) | +55.47 pp | 42 (16.41%) |
| 20261117233 | 50 (19.53%) | 181 (70.70%) | +51.17 pp | 15 (5.86%) |
| 20261117239 | 55 (21.48%) | 203 (79.30%) | +57.81 pp | 40 (15.63%) |
| 20261117241 | 50 (19.53%) | 191 (74.61%) | +55.08 pp | 29 (11.33%) |
| 20261117251 | 56 (21.88%) | 201 (78.52%) | +56.64 pp | 44 (17.19%) |
| 20261117257 | 57 (22.27%) | 182 (71.09%) | +48.83 pp | 36 (14.06%) |
| **Six-seed mean** | **315/1,536 (20.51%)** | **1,147/1,536 (74.67%)** | **+54.17 pp** | **206/1,536 (13.41%)** |

The registered original first-run mean gain is **832/1,536 = 0.5416666667**, with 6/6 positive paired seeds. The exact one-sided sign-flip distribution over all 64 assignments has one outcome at least as extreme: **p=1/64=0.015625**. The precommitted primary replication criterion, requiring at least 5/6 positive seeds, mean gain at least 0.20 and p≤0.05, **passes**. The distinct competence gate **fails**: all six high-diversity models exceed 70% queried-answer accuracy, while zero of six reach 50% complete eight-row table recovery.

A second GitHub Actions CPU training run repeated exactly the same source/example schedules and nominal model seeds. Its mean gain was **+54.62 percentage points**, with the same preregistered primary PASS and competence FAIL outcomes, but only **2 of the 12** checkpoint SHA-256 files are byte-identical across the two hosted trainings. The maximum absolute per-seed gain difference is **0.02734375**. The second result is therefore a numerical portability check on a correlated cohort, with evidence of environment-dependent parameter-fitting differences. ROC-05B pins the **first** trained checkpoint bytes to prevent post-result substitution. The original first-run complete reproducibility archive, including original checkpoints, six full model receipts, raw development predictions, and a **48-file SHA-256 manifest**, has hash **7e21395a51eb5a6db6d51a0e88a04a099b078627eb9a649e818911940a582f10**.

This is a new-source and new-model-initialization repetition of the ROC-04 training-distribution intervention. It supports reproducible queried-answer transfer improvements from broader literal-table exposure under the fixed architecture and optimizer cost. The explicit final-query table-row selector remains a designed inductive bias. Full-table reconstruction remains weak relative to the symbolic direct-lookup oracle.

### ROC-05B: equal-physical-dose hidden rank-seven versus source-input intervention

[ROC-05B, merged LoopedTransformers PR #163](https://github.com/MoralityLabAI/LoopedTransformers/pull/163), registered the causal protocol at commit ef18aef009e72c0b0e75de9331d6135db7977d98, before causal measurements. The original ROC-05A development task scores were already inspected, so its causal result is a **development-family diagnostic**, not a newly sealed model/observer test. The experiment fixes all twelve original first-run model checkpoint SHA-256 values, and every original ROC-05 train/development source hash.

The intervention state lies **after the first four of eight** pre-query tied recurrent steps, with the final visible query held fixed. A rank-seven observer is constructed solely from the matching training hidden states and correct-answer labels, avoiding the eighth centered-label singular direction. A legal early source-A table-row swap changes the exact answer from y to y′ while preserving the final query and intermediate distractors. The original remaining four recurrent steps and native query-selected table head score each direction.

The source edit induces a hidden-state difference. The predeclared interventions compare its normalized projection onto the supervised rank-seven span with its dark complement and train-only PCA rank-seven projector, alongside the full input-induced hidden direction and seeded random controls. The independent input comparator interpolates the early rule-table encoded features on the continuous path between original and legal input until its hidden midpoint displacement reaches the same L2 radius, using a fixed 64-cell bracket and 24 bisections. Radii 0.05, 0.10 and **primary 0.20** are fixed. These intermediate inputs are **off the valid discrete symbolic manifold**, so the measured new-target margin is a sensitivity measure relative to the legally edited target, rather than correct discrete-rule behavior for the interpolated input.

For native final logits z, old correct answer y and legally changed correct answer y′, the endpoint is the change in target margin: g=(z′[y′]−z′[y])−(z[y′]−z[y]). The primary registered test uses all high-512 model seeds and the mean within-seed difference between rank-seven observed-source steering and soft-source-input steering at hidden midpoint radius 0.20, on paired eligible cases. All **256/256** dev cases are physically eligible for each of the six high-diversity models.

| Frozen model seed | Rank-seven observed-rule margin gain | Same-L2 soft-input margin gain | Observed minus input |
|---|---:|---:|---:|
| 20261117231 | +0.117114 | +0.197126 | **−0.080012** |
| 20261117233 | +0.107219 | +0.180734 | **−0.073514** |
| 20261117239 | +0.130885 | +0.186401 | **−0.055517** |
| 20261117241 | +0.120991 | +0.186984 | **−0.065994** |
| 20261117251 | +0.113885 | +0.185136 | **−0.071252** |
| 20261117257 | +0.117713 | +0.179745 | **−0.062032** |
| **Mean** | **+0.117968** | **+0.186022** | **−0.06805338** |

The registered primary mechanism criterion **fails**. The high-512 rank-seven observed-source route has **0/6** positive paired differences relative to equal-L2 input interpolation. Its exact one-sided six-sign p-value in the registered positive direction is **1.0**. The absolute mean difference is **−0.06805337873205038** in original-native-logit target-margin units. A post-hoc reverse-direction statement would require its own registration and independent source/model cohort. These measurements establish sensitivity to this intervention route at a fixed physical cost, with source-family selection exposure already present.

There is an independent semantic check on the full **legal** edit at natural physical dose. The high models answer the legitimately changed source-rule problem correctly on **1,157/1,536 = 75.33%** of cases, compared with **1,147/1,536 = 74.67%** unedited. The lower-diversity models score 326/1,536 = 21.22% on the legal changed source and 315/1,536 = 20.51% unedited. Thus the high-diversity model responds to a valid early source-binding change with substantially stronger task accuracy, even though the selected rank-seven hidden projection produces less new-target margin than the continuous input control at equal physical midpoint dose.

On two fixed exposed development shadow states per model, ROC-05B also measures the four-step suffix Jacobian T, computed change D=T−I, within and cross-observer A/B/C blocks, and fixed-query future-logit output Gram. All cards use exactly **128 keyed rank-matched Gaussian/QR random subspaces**, six one-sided add-one probabilities, and complete Holm adjustment under ROC-01 Amendment C. For the high-512 supervised rank-seven observers, mean null ratios are **A 4.969**, **B 1.749** and **C 1.550**, with **26.31%** mean future-logit Jacobian energy capture. All **48** cards across twelve models, two fixed states and two observer types remain **unclassified** under the complete diagnostic predicates. The observer's output sensitivity and cross-channel geometry consequently provide no full ROC-01 local mechanism diagnosis.

The [hosted original-model causal run](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44107080894) passed a standard-library audit of **73,728** model/case/radius/route effect rows, all **48** null cards, original model/source hashes, native midpoint parity and signed-permutation statistics. The final **69-file SHA-256-indexed** reproducibility archive includes all twelve first-run model checkpoints and their receipts, the source data and all causal rows; its standalone ZIP SHA-256 is **752729e84c30b92ef530591e2b3404df3869c037480eff244042adf07342987a**.

A separately audited [full-null hosted replay](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44107680072) also publishes **3,072 raw null subspace measurements** and independently recomputes the null medians and all **288** one-sided empirical-tail/Holm values for these 48 cards, while retaining the original model weights and 73,728 causal rows. Its standalone archive SHA-256 is `384c3e8760e8e8ec23666734fb8f15ae1bc4f134436262a1f8e4123986934acb`; the primary mean differs by approximately 5.17×10⁻⁹ margin units from the first replay and still has 0/6 positive seeds and p=1.0. This raw-null audit is part of [LoopedTransformers #165](https://github.com/MoralityLabAI/LoopedTransformers/pull/165); the two archive versions and their identical scientific inference are detailed in the [reproducibility addendum](ROC05B_FULL_NULL_REPRODUCIBILITY_ADDENDUM.md).

### Interpretation and prospective boundary

ROC-04A/B showed rule-identity transfer on the original training cohort, ROC-05A replicated the training-distribution effect with new source permutations and six new model seeds, and ROC-05B found a registered negative response for a train-only rank-seven hidden-state source steering route in those stronger models. The appropriate mechanistic reading is specific: **learned queried-answer competence and future-logit sensitivity capture can coexist with substantial dark-to-observed computed-change coupling and failure of the selected rank-seven source-steering comparator**. The source-input comparator is off-manifold and calibrated by physical hidden midpoint L2; its margin gain is not independent legal input task accuracy. The legal full-input rule-edit results remain separately grounded in the symbolic reference interpreter.

These experiments cannot certify exact storage of all eight rule rows, a minimal closed recurrent quotient, or an exhaustive observer intervention cover. A future sealed source comparison requires a new protocol and evaluation with no outcome-driven model or rank selection. The 384 ROC-05 reserved table identities have **no generated input cases or labels**, and the original ROC-02 family-6/7 test sources remain unopened.


## Dated postscript: ROC-06A train-only counterfactual-gradient observation (25 November 2026)

[ROC-06A LoopedTransformers PR #361](https://github.com/MoralityLabAI/LoopedTransformers/pull/361) registered its scientific protocol at commit `1c209f6db0f56dd0bb4d4677d1fb22a8cd462a8c`, before evaluating the new gradient-observer intervention. The six original 512-rule and six original four-rule models retain the first complete ROC-05A training-run checkpoint bytes; each checkpoint and all three train/development source files pass their original SHA-256 identity gates. No new model optimizer step occurs. ROC-06A uses the same 256 **previously exposed development cases** per model; the ROC-05 384-table reserved set remains ungenerated, and original ROC-02 source families 6–7 remain unopened.

For each of 1,024 training cases in the corresponding model arm, a legal early source-A binding-table output swap gives a new exact target y′ while holding the final query q fixed. From the original pre-query midpoint h, the study differentiates the **original frozen four-step suffix changed-target margin**, \(g=\nabla_h[z_{y'}(h,q)-z_y(h,q)]\). A four-step analytic reverse-mode VJP passes numerical comparison against PyTorch autograd and directional finite differences. Individual nonzero training gradients are L2 normalized, mean-centered across training cases, and a rank-seven orthogonal observer is formed from the top seven right singular directions. The supervised task-label observer and the train-only PCA reference retain the prior ROC-05B fitting procedure.

The same legal rule edits are evaluated on all exposed development cases. Source-induced hidden changes projected into each train-only observer are scaled to hidden midpoint L2 radius 0.05, 0.10 and primary **0.20**. The physically matched input comparator interpolates the encoded early source table to the same hidden midpoint radius via a fixed 64-cell search and 24 bisections. This softened input lies off the legal rule-table manifold. Every output gain is measured in the original native logits after the original remaining four recurrent updates and fixed query-selected table-head row.

The **single registered primary** is the six-seed mean of gradient-projected margin gain minus the **larger of two predeclared seed-mean controls**, supervised projected steering and softened input, on exactly the same triple-eligible cases. A valid positive claim needs ≥205/256 eligible case triplets per seed, at least five positive seed differences, positive unweighted mean and exact one-sided p≤0.05 across 64 sign assignments.

| Original high-512 seed | Gradient-observed gain | Supervised-observed gain | Equal-L2 softened input | Gradient minus best |
|---|---:|---:|---:|---:|
| 20261117231 | +0.130745 | +0.117114 | +0.197126 | **-0.066381** |
| 20261117233 | +0.125644 | +0.107219 | +0.180734 | **-0.055090** |
| 20261117239 | +0.135669 | +0.130885 | +0.186401 | **-0.050732** |
| 20261117241 | +0.131419 | +0.120991 | +0.186984 | **-0.055565** |
| 20261117251 | +0.130900 | +0.113885 | +0.185136 | **-0.054236** |
| 20261117257 | +0.121885 | +0.117713 | +0.179745 | **-0.057860** |
| **Six-seed mean** | **+0.129377** | **+0.117968** | **+0.186021** | **−0.056644** |

All six high-diversity models have **256/256 valid three-way case comparisons**. The gradient observer's hidden margin gain increases **+0.01140925** over supervised rank seven, positive in every model seed. This secondary difference has one-sided sign-flip p=1/64 as a descriptive statistic; the more demanding registered primary compares against the larger reference. The softened-input mean is larger in every high seed. The gradient-minus-best result is **−0.0566440431951681**, with **0/6 positive seeds** and **one-sided exact p=1.0**, so **the ROC-06A registered primary FAILS**. The full legal discrete changed-source input retains **1,157/1,536 = 75.33%** correct changed targets; unedited high models achieve 1,147/1,536 = 74.67% correct.

Across twelve frozen models and two fixed development shadow states, each rank-seven gradient/supervised/PCA observer is compared with 128 SHA-keyed same-rank Gaussian/QR null subspaces. The complete audit verifies **92,160** model/case/radius/route records, **3,072** raw null measurements, **72** observer cards and **432** six-tail empirical p/Holm values. All **72/72** local mechanism cards remain unclassified. High-model gradient-observer B/null is **1.780×** with **31.51%** native future-logit energy captured, compared with supervised B/null **1.749×** and capture **26.31%**. The gradient basis's top seven centered train-normalized singular directions capture approximately **34.13%** of the corresponding gradient-variation energy.

The [gradient-geometry mathematical note](https://github.com/MoralityLabAI/LoopedTransformers/blob/main/experiments/roc06_train_gradient_observer/GRADIENT_GEOMETRY_JOURNAL.md) makes the source of the gap explicit. The rank-seven gradient basis maximizes its **training gradient-variation energy** by the Ky Fan variational principle. Actual small-radius signed steering for a legal source-induced state displacement δ depends on \(g^\top P\delta/\|P\delta\|\); maximizing captured gradient magnitude alone does not fix the alignment or sign of the source displacement. The model's supplied visible query-to-table route also remains an architectural inductive bias.

The independent [hosted full CPU replay #45569749676](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/45569749676) passed analytic gradient preflight, all six original model-seed jobs, the full causal/geometry receipt audit and the public six-seed arithmetic. Its 69-file standalone reproduction archive SHA-256 is `f0ca87809dd3675dab7baee4e7d02743e97301cffb96dc772e2cb7d2700f9093`; the bundle includes the twelve original checkpoint bytes, the SHA-pinned original source, all per-case outputs, raw nulls and scripts. The initial preflight and subsequent study-label wrapper corrections are documented in the [merged ROC-06A result report](https://github.com/MoralityLabAI/LoopedTransformers/blob/main/experiments/roc06_train_gradient_observer/ROC06A_CAUSAL_RESULT.md) without changing the preregistered comparison.

This result is a **negative same-dose physical intervention result for one train-derived rank-seven gradient observer** on previously exposed development data. It accompanies positive queried-answer transfer from diverse rule training. Both mechanistic conclusions and future source-generalization claims require separately registered experiments.

## Reproducibility and source record

- Original ROC-02 source, model binaries and split manifest: [LoopedTransformers delayed-rule experiment](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/roc02_delayed_rule_v1).
- ROC-02B rank/null paper receipts: [merged #124](https://github.com/MoralityLabAI/LoopedTransformers/pull/124).
- ROC-02C equal-budget code, twelve model receipts, public data, checkpoint replay workflow: [merged #144](https://github.com/MoralityLabAI/LoopedTransformers/pull/144).
- ROC-02E preregistration at `8fc97c97d9ed37a6a312933bc2040f5cc603d0c6` and 256-pair causal analysis: [PR #147](https://github.com/MoralityLabAI/LoopedTransformers/pull/147). Complete model-level and paired CSVs are in `experiments/roc02_delayed_rule_v1/roc02e_calibration/`; 516,096 per-case records have a downloadable, source-verified hosted artifact.
- ROC-04A frozen 4-versus-512 protocol, exact source hashes, archived six-seed model receipts, legal control rows, and independent six-seed audit: [merged LoopedTransformers #155](https://github.com/MoralityLabAI/LoopedTransformers/pull/155), [result report](https://github.com/MoralityLabAI/LoopedTransformers/blob/main/experiments/roc04_permutation_transfer/ROC04A_SIX_SEED_RESULT.md) and [hosted complete replay](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44085250022).
- ROC-04B independent 384-rule permutation confirmation: [merged LoopedTransformers PR #157](https://github.com/MoralityLabAI/LoopedTransformers/pull/157), [confirmed experiment report](https://github.com/MoralityLabAI/LoopedTransformers/blob/main/experiments/roc04_permutation_transfer/ROC04B_RESERVED_TEST_RESULT.md), and [successful hosted independent test](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44087829448). The test source SHA and 16-member reproducibility manifest are pinned above.
- ROC-05A independent model-seed/source-pool replication: [merged LoopedTransformers #162](https://github.com/MoralityLabAI/LoopedTransformers/pull/162), [original first-run result and portability report](https://github.com/MoralityLabAI/LoopedTransformers/blob/main/experiments/roc05_fresh_replication/ROC05A_PRIMARY_RESULT.md), plus independent [full hosted repeat run](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44103113334).
- ROC-05B physical source/hidden intervention: [merged LoopedTransformers #163](https://github.com/MoralityLabAI/LoopedTransformers/pull/163), [registered causal result and observer null-cards](https://github.com/MoralityLabAI/LoopedTransformers/blob/main/experiments/roc05_fresh_replication/ROC05B_MATCHED_CAUSAL_RESULT.md), and [hosted original frozen-model audit](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44107080894).
- ROC-06A counterfactual-gradient rank-seven observer and negative conservative physical comparison: [merged LoopedTransformers #361](https://github.com/MoralityLabAI/LoopedTransformers/pull/361), [full hosted run #45569749676](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/45569749676), [ROC-06A report](https://github.com/MoralityLabAI/LoopedTransformers/blob/main/experiments/roc06_train_gradient_observer/ROC06A_CAUSAL_RESULT.md).
- Reference ROC-01 theory and dated Amendment C: [MathCan PR #99](https://github.com/patrickdugan/MathCan/pull/99).
- Companion numerical-range manuscript v0.6: [MathCan PR #87](https://github.com/patrickdugan/MathCan/pull/87). Its earlier NRF-09/11 results use different models, folds and coupling normalizations. Their experimental counts have **not** been pooled into ROC-02.

The ROC-02E exact six-seed sign-flip replay is in papers/roc02/roc02_primary_signflip_v01.py. ROC-04A and ROC-04B have their own copied original seed tables and standard-library checkers. ROC-05A's original first-run six-seed table and ROC-05B's frozen causal paired table are preserved byte-identically from LoopedTransformers as ROC05A_fresh_seed_primary_v01.csv and ROC05B_matched_causal_primary_v01.csv. The companion roc05a_b_primary_audit_v01.py independently checks both original Git blob hashes, all six-seed arithmetic, the exact 64-sign tests and the separate competence/causal gates. All scripts retain the appropriate exposed-development or reserved-source inference scope.
