# Leakage-regularized recurrent observers improve calibration, but fail a matched rule-intervention test

**ROC-02 empirical paper update · version 0.1 · 17 November 2026**

*MoralityLabAI / MathCan research note. Experimental subject: 128-dimensional parameter-tied residual networks on an eight-class delayed rule-binding task.*

## Abstract

Low-rank observers of recurrent hidden states are often evaluated by their reconstruction error, local Jacobian closure, or capture of the model's future output sensitivity. We study whether reducing the incoming computed-change coupling of a trained low-rank observer also produces an advantage on an input-grounded causal intervention. Twelve frozen recurrent models, with six seeds at each of depths 8 and 16, are trained for 240 AdamW steps on delayed-rule source families 0–3. The original networks reach mean accuracy of 21.55% and 22.40% on exposed calibration families 4–5. In the subsequent ROC-02C equal-budget observer pilot, leakage-regularized rank-7 and rank-8 observers improve calibration mean squared error and rank-matched null-normalized incoming coupling over task-only observers in all 24 model-rank comparisons. At depth 16, rank 7, mean task MSE changes from 0.1058 to 0.0976, while normalized squared incoming coupling changes from 2.783 to 0.0385. A preregistered ROC-02E causal test then contrasts early stored-rule edits against late query-cue edits, whose legal counterfactuals share the same correct target. With 256 exposed calibration cases per model and a hidden midpoint intervention norm of 0.20, the depth-16, rank-7, rule-induced observer-steering effect is +0.00014148 in original-model target-margin gain relative to task-only. Three of six seeds favor the regularized observer; the exact one-sided six-seed sign-flip p-value is 0.375. A strong within-calibration geometric objective therefore fails to predict a consistent rule-specific causal advantage in this short-trained model cohort. The sealed source families 6–7 remain untouched. These results are a negative **calibration-family causal diagnostic**, with both observer hyperparameter selection and causal evaluation using families 4–5.

## 1. Research question and evidence sequence

A recurrent model evolves a hidden state through tied transformations. A rank-\(k\) observer reads only the coordinates along an orthonormal basis \(U\). The ROC-01 calculus separates what changes within that subspace from what enters it from its dark complement and what leaves it. A small incoming-coupling block is attractive as a closure diagnostic, especially when a low-rank readout still predicts the training objective.

The immediate empirical question is sharper: **Does the leakage-regularized observer react to an authentic change of the remembered source rule more usefully than an equally trained task observer or a same-dose input control?** The study uses already trained and frozen neural networks. Its primary endpoint is obtained from their original final logits after physically matched hidden-state interventions, rather than from a refitted observer head.

The evidence sequence has a dependency structure:

- **ROC-02:** fixed source generator and twelve 240-update model checkpoints, including SHA-256 source and weight receipts; train families 0–3, calibration families 4–5, unopened procedural holdout 6–7. [Source and training](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/roc02_delayed_rule_v1).
- **ROC-02B:** a preregistered nine-rank pilot with 128 SHA-keyed rank-matched null subspaces per state, 27,648 published null rows, and original future-logit Jacobian capture. All 432 observer-state cards remain unclassified under the complete ROC-01 Amendment C criteria. [Merged PR #124](https://github.com/MoralityLabAI/LoopedTransformers/pull/124).
- **ROC-02C:** equal-budget, 80-step optimization of rank-7 and rank-8 observers, with calibration-selected regularization. [Merged PR #144](https://github.com/MoralityLabAI/LoopedTransformers/pull/144).
- **ROC-02E:** physically controlled rule-versus-cue intervention using the newer ROC-02C observers, with 256 paired calibration records per model. [PR #147](https://github.com/MoralityLabAI/LoopedTransformers/pull/147).

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

The next registered cohort should train the delayed-rule model to stronger **train and calibration accuracy under a source lock**, then freeze the architecture, observer selection, causal protocol, and checkpoint SHA before consulting any untouched family. A simple deterministic symbolic table interpreter already solves the generated task by construction, establishing its exact answer and exposing a useful model-capability gap. The new cohort needs an equal-budget task-only observer, full rank-matched nulls, true source/cue/distractor changes, and six-seed paired analysis. A positive result requires correct counterfactual-rule behavior above an implementable equal-cost input policy and prespecified multiple-testing control.

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

Together the two follow-ups separate failure modes: the original linear-readout recurrent model struggles even on its training examples after longer optimization, while the query-conditioned table-decoder fits those four training rule families perfectly and fails to transfer to unseen tables. The source-family generator needs broader combinatorial training support, with a newly frozen, genuinely unseen permutation-family split and equal-budget controls, before using these models to test a learned causal quotient. Families 6 and 7 from the original ROC-02 sealed test remain unopened.

## Reproducibility and source record

- Original ROC-02 source, model binaries and split manifest: [LoopedTransformers delayed-rule experiment](https://github.com/MoralityLabAI/LoopedTransformers/tree/main/experiments/roc02_delayed_rule_v1).
- ROC-02B rank/null paper receipts: [merged #124](https://github.com/MoralityLabAI/LoopedTransformers/pull/124).
- ROC-02C equal-budget code, twelve model receipts, public data, checkpoint replay workflow: [merged #144](https://github.com/MoralityLabAI/LoopedTransformers/pull/144).
- ROC-02E preregistration at `8fc97c97d9ed37a6a312933bc2040f5cc603d0c6` and 256-pair causal analysis: [PR #147](https://github.com/MoralityLabAI/LoopedTransformers/pull/147). Complete model-level and paired CSVs are in `experiments/roc02_delayed_rule_v1/roc02e_calibration/`; 516,096 per-case records have a downloadable, source-verified hosted artifact.
- Reference ROC-01 theory and dated Amendment C: [MathCan PR #99](https://github.com/patrickdugan/MathCan/pull/99).
- Companion numerical-range manuscript v0.6: [MathCan PR #87](https://github.com/patrickdugan/MathCan/pull/87). Its earlier NRF-09/11 results use different models, folds and coupling normalizations. Their experimental counts have **not** been pooled into ROC-02.

The six-vector exact sign-flip replay in `papers/roc02/roc02_primary_signflip_v01.py` is a stdlib-only arithmetic check of the stated registered statistic.
