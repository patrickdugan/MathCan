# ROC-02A: frozen NRF checkpoint rank sweep with causal-output capture

**Status:** retrospective, source-locked pilot; November 16, 2026. Registered before the first new rank/null measurements in [`configs/roc02a_frozen_nrf_rank_causal_pilot_v1.json`](../../configs/roc02a_frozen_nrf_rank_causal_pilot_v1.json), commit `650c61b35b46b9c74a75e988090bfead2de7c348`. This study uses archived NRF-09/11 model seeds and task folds. It is **separate from** the prospective ROC-02 delayed-rule binding experiment in MathCan ROC-01 Amendment C.

## Design and provenance

All six original NRF-09 seeds (131, 137, 139, 149, 151, 157) at trained depths 16 and 32 and 32 optimizer updates were loaded from their **original saved .pt file bytes**. The twelve 8D task-only and leakage-aware observer adapters are the frozen NRF-11 selections. Before evaluation the script checks both SHA-256 values against each NRF-11 companion receipt. Model weights, original optimizer parameters, and frozen rank-eight observer bases are unchanged.

The registered rank grid is `{1,2,3,4,7,8,12,16,32}`. At every rank the study fits a train-only cross-covariance/SVD basis, with train-only residual PCA for extra dimensions at ranks above 8, and a train-only PCA comparator. At rank 8 it additionally reads the two **frozen NRF-11** task-only and leakage-aware observer bases. All four observer types use the same train-only ridge predictor and the same held-out task fold 12 (96 examples); fold 1 contains 160 training examples. Exactly two shadow midpoint states, indices 0 and 1 of the preexisting fold-13 generator, are evaluated per model. The other ten states per model are outside this bounded pilot.

A separate **train-only reference output map** is fitted by ridge regression from the network's final 128D recurrent state to its original eight signed-permutation task labels. Its frozen future-output Jacobian from midpoint state `h_(R/2)` is `G = C_output T`, with `T = D(F^(R/2))(h)` and `C_output` the fitted 8-by-128 matrix. The ROC causal-output Gram is `H = GᵀG` and `s(U)=tr(UᵀHU)/tr(H)`. The reference head is a secondary measurement instrument trained from fold 1, **not** the native network output head, a new reasoning capability, or independent labels. The reference head's held-out task MSE averages approximately 0.136 (R16) and 0.241 (R32), and is explicitly reported per model in the raw observer file.

For `D=T-I`, the exact `A=UᵀDU`, `B=UᵀDQ`, `C=QDU` Frobenius blocks are reported both as raw norms per `sqrt(k)` and divided by `||D||_F`. (Here Q is an orthogonal complement, so the recorded norm of C equals `|| (I-UUᵀ) D U ||_F`.) The controls use **128** SHA-256-keyed Gaussian/QR rank-matched subspaces per checkpoint, state, and rank, seeds 941001..941128, with distinct projector fingerprints. This yields 216 state/rank groups and **27,648 random-null rows**. Empirical rank-based p-values use `(1+#ties-or-more-extreme)/129` and the **six** predeclared one-sided ROC-01 Amendment-C directions with Holm correction. A complete copy is in the reproduction archive; the repo's compressed CSV preserves all numeric null scores and the first 128 bits of each projector fingerprint, enough to recalculate every empirical p and median.

## Rank-eight results: one new reference-head capture endpoint

The entries are arithmetic means over six independent model seeds, with two preregistered shadow states per model for local Jacobians. `B/random` is the mean of each shadow state's ratio of `||B||/||D||` to its 128-random-rank-eight median. The capture `s` is the fraction of the **fitted future reference head's** output-Jacobian energy supported in the observation subspace. `E` is fresh-fold-12 task MSE.

| Depth | Observer | E | B/random | Capture s | Observed finite Δoutput (radius .2) | Dark finite Δoutput (radius .2) |
|---|---|---:|---:|---:|---:|---:|
| 16 | Supervised SVD | 0.245731 | 1.0203 | 0.4324 | 0.09438 | 0.03151 |
| 16 | Task-only, frozen k8 | 0.128465 | 0.9222 | 0.9115 | 0.14039 | 0.01185 |
| 16 | Leakage-aware, frozen k8 | 0.153759 | 0.7742 | 0.8701 | 0.13738 | 0.01465 |
| 16 | Train-only PCA | 0.383895 | 1.1069 | 0.0394 | 0.02894 | 0.03809 |
| 32 | Supervised SVD | 0.284454 | 1.1688 | 0.3105 | 0.08803 | 0.03231 |
| 32 | Task-only, frozen k8 | 0.157141 | 0.7158 | 0.6736 | 0.12470 | 0.01926 |
| 32 | Leakage-aware, frozen k8 | 0.247049 | 0.4423 | 0.5366 | 0.11217 | 0.02564 |
| 32 | Train-only PCA | 0.386935 | 1.3882 | 0.0240 | 0.02436 | 0.03635 |

At depth 32, moving from task-only to the frozen leakage-aware basis lowers the null-relative incoming block in **6/6 model seeds**, and also lowers output Gram capture in **6/6**, while task error rises in **6/6**. Capture falls from 0.6736 to 0.5366 (about 20.3% relative). Because the actual output head was fitted on the same training family and the two states are within already exposed fold 13, this is a **retrospective causal-output sensitivity diagnostic**, not a new family-level generalization claim.

Both frozen k8 optimized arms have Holm-corrected **upper-tail output capture p <= 0.05 in 12/12 sampled states** at each depth; their capture is still substantially above the rank-eight random baseline. The depth-32 leakage-aware observer's `B/random` is low but above the amendment-C strict small-`B` effect threshold (relative 0.20), so the card must **not** be labeled an exact closed quotient. The recorded six-tail p-values allow any future threshold check; the paper does not infer a causal mechanism type from their sign alone.

## Rank sweep and output-rank tradeoff

At depth 32, the supervised rank-grid means include:

| k | Supervised task E | Output capture s | B / rank-null median |
|---:|---:|---:|---:|
| 1 | 0.3861 | 0.039 | 1.241 |
| 4 | 0.3425 | 0.152 | 1.218 |
| 7 | 0.3025 | 0.272 | 1.180 |
| 8 | 0.2845 | 0.310 | 1.169 |
| 16 | 0.2798 | 0.323 | 1.269 |
| 32 | 0.2696 | 0.356 | 1.267 |

The sweep finds the task-trained rank-eight basis substantially above rank-matched random in causal-output capture, while simple train-only PCA is consistently below the corresponding random capture median. Enlarging the **unoptimized** supervised basis beyond k=8 offers modest held-out gains and does not by itself lower `B/random`. The full odd/even rank grid, paired model-seed MSE, causal capture, and 3D nondominated `(k,E,B/random)` membership are in the source-derived CSVs. This is a measured frontier **of the registered candidate families**, not a claim of a globally optimized rank-k leakage floor.

## Direct physical perturbations

For each selected state and rank, a deterministic seeded Gaussian vector is projected into `span(U)`, projected into its orthogonal complement, and used unprojected as an isotropic control. All three are normalized to **physical L2 radius 0.2** and passed through the unchanged suffix and frozen fitted final-output head. An independent tangent prediction `G delta` is compared with each true nonlinear output change. The source additionally includes the **ablate-U-at-readout** control of the rank-k midpoint decoder: replacing the fit prediction with its training-label mean, reporting both task-error change and output shift. These distinct interventions answer distinct questions; the readout ablation is not treated as a hidden-state transplant.

At depth 32 the mean finite output change for an observed-subspace perturbation goes from 0.12470 (task-only) to 0.11217 (joint), and dark-direction perturbation from 0.01926 to 0.02564. The dark-direction effect rises in **5/6 seeds** with the joint observer, despite the lower observer-specific `B` block. Directions change when U changes, so these perturbation contrasts are **direction-conditioned**, not a matched-vector causal effect of training. The analytic output Gram `s` gives the basis-invariant counterpart. A small local tangent residual is a computational check on the finite-radius replay, not an independent proof of nonlinear global behavior.

## Files, evidence limits, and continuation

- `research_gym/analysis/roc02a_frozen_rank_causal.py` performs gated checkpoint load, rank sweep, full-Jacobian measurement, 128-null generation, Holm tests, and finite interventions.
- `research_gym/analysis/roc02a_summarize.py` writes 12-model paired rank summaries, 3D Pareto membership and null-median checks.
- `roc02a_rank_nulls_compact.csv.gz` publishes the 27,648 random rows (gzip, one CSV after decompression). `roc02a_rank_null_medians.csv` and `roc02a_rank_by_seed.csv` are smaller cross-checks.
- `roc02a_rank_observers.csv` contains all 480 candidate state/rank/observer results, including Gramian energy, all six rank-based p and Holm q, actual causal finite changes and readout ablation risk.
- Tests check actual archived checkpoint/adapters where available; hosted source tests skip binary-dependent cases and use public receipt arithmetic. The separate archive contains raw full-precision nulls and the original 24 binary source files.

**Limits:** Six **short-trained** original model seeds, 32 weight updates each, one synthetic Gaussian task family, two already exposed states, a separately fitted reference head, retrospectively assessed observer bases (k8) and a partial rank sweep. The measured rank-null p values condition on checkpoint and state; the independent statistical unit for model-level findings remains a model seed. The observed mechanism cannot certify invariance, latent rule storage, generalization to reasoning tasks, or safety.

**Prospective next experiment:** ROC-02 delayed-rule binding/release on six new model seeds, source-family-disjoint splits, exact symbolic interpreter, calibration-only fitting, 128 null bases per state/rank, correct physical intervention set and matched random controls, and sealed tests as amended in ROC-01 Amendment C. This pilot's outcomes must not retune that prospective registration.