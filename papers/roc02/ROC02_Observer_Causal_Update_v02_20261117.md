# Recurrent observers, rule-specific causal tests, and permutation-transfer competence

**ROC-02–04 empirical paper update · version 0.2 · 17 November 2026**

*MoralityLabAI / MathCan research note. Experimental subject: 128-dimensional parameter-tied residual networks on an eight-class delayed rule-binding task, and a later query-conditioned table-memory model.*

## Abstract

Low-dimensional observers of recurrent hidden states are often selected by task reconstruction error, local Jacobian closure, and future-output sensitivity. ROC-02 tests whether suppressing dark-to-observed computed-change coupling gives an intervention-level advantage. Across twelve frozen depth-8/16 residual models, regularized rank-7/8 observers improve calibration MSE and rank-matched null-normalized coupling over equal-budget task-only observers in all 24 model-rank comparisons. A registered input-grounded rule-edit intervention, ROC-02E, then yields a mean original-logit target-margin gain of only +0.00014148 relative to task-only at depth 16/rank 7, with three of six positive seeds and a one-sided exact sign-flip p-value of 0.375. The original model's delayed-rule calibration accuracy is around 22%, which limits the interpretation of its future-logit Jacobian.

ROC-03A and ROC-03B expose task-learning limitations: increased training of the original recurrent model leaves large training errors, while a query-conditioned table decoder reaches perfect training accuracy on four affine rule families yet reconstructs zero complete tables on 256 different calibration-family cases. ROC-04A directly varies rule diversity at fixed model architecture, example count, optimizer exposure, initialization and schedule. On a new exposed set of 256 unseen permutation tables, six matched seeds trained with 512 distinct tables improve mean queried-answer accuracy from **22.92% to 70.70%**, a **+47.79 percentage-point** gain (6/6 positive seed differences; one-sided sign-flip **p=0.015625**). The preregistered primary transfer gate passes. The separate competence gate fails: complete eight-row table recovery averages **11.13%**, with 0/6 seeds meeting its 50% requirement. Legal rule-table edits elicit 73.76% mean changed-answer accuracy; label-preserving distractor edits retain predictions on 92.53% of eligible cases.

The combined evidence separates observer-geometry optimization, rule-sensitive causal behavior, and learning under diverse source distributions. ROC-02's source families 6–7 and ROC-04's separate 384-table reserved evaluation remain unopened. ROC-04A supports a strong improvement on **exposed development permutations**, with full-table recovery and an independent prospective causal-mechanism test still outstanding.

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

ROC-04A already selected and evaluated its fixed models on exposed development permutations. Its separate **384-table reserved evaluation** must follow a frozen ROC-04B test protocol and published checkpoint/source hashes to test rule-identity transfer outside this dev pool. That future test will require a distinct label-release record, with no refitting or model choice afterward. ROC-01's low-rank A/B/C/H closure classification and equal-dose causal control program remain further experiments even if reserved-set queried-answer competence succeeds. The original ROC-02 sealed families 6–7 belong to an independent procedural holdout and have not been opened.

## Reproducibility and source record

- Original ROC-02 source, model binaries and split manifest: [LoopedTransformers delayed-rule experiment](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/roc02_delayed_rule_v1).
- ROC-02B rank/null paper receipts: [merged #124](https://github.com/MoralityLabAI/LoopedTransformers/pull/124).
- ROC-02C equal-budget code, twelve model receipts, public data, checkpoint replay workflow: [merged #144](https://github.com/MoralityLabAI/LoopedTransformers/pull/144).
- ROC-02E preregistration at `8fc97c97d9ed37a6a312933bc2040f5cc603d0c6` and 256-pair causal analysis: [PR #147](https://github.com/MoralityLabAI/LoopedTransformers/pull/147). Complete model-level and paired CSVs are in `experiments/roc02_delayed_rule_v1/roc02e_calibration/`; 516,096 per-case records have a downloadable, source-verified hosted artifact.
- ROC-04A frozen 4-versus-512 protocol, exact source hashes, archived six-seed model receipts, legal control rows, and independent six-seed audit: [merged LoopedTransformers #155](https://github.com/MoralityLabAI/LoopedTransformers/pull/155), [result report](https://github.com/MoralityLabAI/LoopedTransformers/blob/main/experiments/roc04_permutation_transfer/ROC04A_SIX_SEED_RESULT.md) and [hosted complete replay](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44085250022).
- Reference ROC-01 theory and dated Amendment C: [MathCan PR #99](https://github.com/patrickdugan/MathCan/pull/99).
- Companion numerical-range manuscript v0.6: [MathCan PR #87](https://github.com/patrickdugan/MathCan/pull/87). Its earlier NRF-09/11 results use different models, folds and coupling normalizations. Their experimental counts have **not** been pooled into ROC-02.

The ROC-02E exact six-seed sign-flip replay is in `papers/roc02/roc02_primary_signflip_v01.py`. ROC-04A's independently copied seed table and exact sign-flip/competence-gate verifier are `ROC04A_primary_six_seed_v01.csv` and `roc04a_primary_signflip_v01.py`. Both scripts use the standard library and retain their respective calibration versus development inference scopes.
