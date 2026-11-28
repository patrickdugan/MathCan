# COE-09: A permutation obstruction to identifying labels from separated histories

Research date: 2026-11-15. Source chain: COE-01..08; original OpenAI Math families #098 and #332 motivate evaluator-relative embedding and the distinction between extension and reconstruction. The results below follow directly from finite combinatorics and orthogonal geometry, independently of either OpenAI paper's unverified deeper claims. The formulation is new to this research campaign; literature-wide novelty is not asserted.

## Theorem A: Complete-graph probe separation is label-blind

Let `X={x_1,...,x_q}` with one state for each distinct target label, `q>=2`. Give the evaluator the complete graph `K_q`. For a code `c:X -> C`, define its distinct-pair score

`S(c) = sum_{i<j} 1[c(x_i) != c(x_j)]`.

Then `S(c∘π)=S(c)` for **every permutation** `π` of the states. Proof: the permutation induces a bijection on unordered distinct pairs and preserves equality of their codes. Consequently, a score of `binom(q,2)` certifies `q` distinct codes, while the score is invariant under arbitrary relabeling of those codes across domains.

This yields a strict classification separation. Let the training domain teach the classifier `d(c(x_i))=i`. On a held-out domain, use exactly the same `q` distinct codes, and assign true labels `π(i)` for any derangement `π`. Pair separation remains maximal in both domains, but the frozen training decoder has 0/q held-out accuracy. A derangement exists for every q>=2 (the cyclic shift `π(i)=i+1 mod q`). Finite K3 witness: code `(0,1,2)`, target `(1,2,0)`, separation `3/3`, classification `0/3` (Lean-certified).

A permutation of *training* label associations relative to frozen codes supplies an identifiable null for held-out decoding. To avoid confounding ties, we compute the null by explicit deterministic relabeling of fit prototypes and recomputing the decoder's fixed smallest-label tie rule; the expected accuracy is not unconditionally `1/q` in an arbitrary tie-heavy, label-imbalanced sample. The COE-09 code keeps the native benchmark's q=9 classes and 18 held-out boards fixed and reports the actual conditional distribution.

**Interpretation.** COE-07's K9 edge-retention score checks that a probe has distinct output values. Held-out label decoding is needed to show that the same values mean the same digit across the fit and test strata. COE-08's shuffled output-trace null addresses a different issue: it tests truth-conditioned correctness histories rather than label-free latent codes.

## Theorem B: Norm-matched dark-fiber rotation preserves current logits exactly

Let `H` be a finite-dimensional real inner-product space, `W:H -> R^m` linear, and `P` the orthogonal projector onto `range(W*)`. Write `x=v+r` with `v=Px`, `r=(I-P)x`. Choose any `u in ker W` with `||u||=1` and `<u,r>=0`, where `||r||>0`. For real angle θ define

`x_θ=v+cos(θ)r+||r||sin(θ)u`.

Then

`P x_θ=v`, `W x_θ=W x`, `||x_θ||^2=||x||^2`, and
`||x_θ-x||=2||r||·|sin(θ/2)|`.

The first two identities follow because both `r` and `u` lie in `ker W`. Pythagoras and the cosine-sine identity give the norm statement. Expanding `||x_θ-x||²` gives `||r||²[(cosθ−1)²+sin²θ]=4||r||²sin²(θ/2)`. Thus every dark intervention is on the original norm sphere and has exactly the same magnitude as any matched-angle random tangent **within the same dark sector**. It can change later recurrent logits, making delayed task effects a causal test of dark-memory relevance.

For a row-space rotation, exchange `v` and `r`: dark coordinates stay fixed and the same total-norm identity holds. For scratchpad `z_L`, rotate its full vector on its own sphere. Each intervention changes only the evaluator-designated target cell at the registered visit. A zero-norm component or missing tangent produces an explicit failure. Random tangents are fixed by seed, matched in radius, and held constant across the fit/test boundary.

The general geometric identities are proved here in ordinary mathematics and checked numerically in PyTorch at float64; the Init-only Lean module formalizes readout-preserving product-state changes and the orthogonal norm accounting implication. Full real Hilbert-space geometry has not been formalized in Lean.

## Protocol and scope

The native primary uses the already pinned `gaoxin492` 7M Attention-TRM with original SHA-256 `932b5e0d...`, the 36-board COE-07 manifest, fit `S1_naked1+S3_prop3plus`, held-out `S2_prop2+S4_stalled`, eight visits. The only candidate heads are preselected COE-07 readouts from fit data. Five decoding choices report ordered, cyclic, dihedral, count and final-bit label accuracy, one observed top-1 digit per held-out board. All tie rules are fixed. A conditional label-shuffle distribution is computed at fixed probe weights.

For the intervention, `cyclic_gain` is selected before evaluation; dark `z_H`, visible `z_H` and scratch `z_L` are each rotated at the evaluator target site after visit four by ±0.05 rad. Control directions use seeds 303 and 317 and identical sector norm and signed angle. Score final visit-eight target accuracy, margin change, prediction flips and current-time row-space/logit parity. The selected and control outcomes are descriptive paired comparisons across 18 boards, with no assumption that pairs of boards are statistically independent. Dark-sector current logits must remain invariant.

The synthetic control replays three frozen COE-04 tied-attention models (seeds 2406, 2407, 2408), with the source readouts frozen and 4 fit/4 heldout contexts, using eight labels. These models trained on all 64 original examples; their probe holdout is over distractor contexts on the trained model, not over base-model training data. Results are a feasibility sanity check, not a pretrained result. The native 7M result and causal effects remain pending until the pinned checkpoint is successfully loaded and both artifacts pass SHA verification.
