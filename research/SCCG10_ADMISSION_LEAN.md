# SCCG-10 stale-observer admission: Lean receipt

Module: `MathCan/SCCG10Admission.lean` (imported from `MathCan.lean`). Core Lean only, toolchain v4.35.0, no Mathlib. Integers stand in for exactly scaled rationals; vectors are `Fin n -> Int`; `dot` is defined by recursion on `n`.

## Theorems
- `stale_target_lower`: f1-f0 = dot a' u + r, |r| <= R, |dot a' u - dot a u| <= E gives f1-f0 >= dot a u - (E+R).
- `stale_protected_linf`: per-row residual and stale-derivative bounds with |(Cu)_i| + E_i + R_i <= eta give |g1 i - g0 i| <= eta for all i.
- `refresh_value_le_gap`: live-feasible gains <= U and cached live gain >= L give v - cached <= U - L.
- `ranking_certificate`: pairwise score-interval separation preserves order.
- `ranking_topset`: Fin-indexed pairwise form over a cached set S (every in-S interval separated from every out-of-S interval).
- `ranking_topset_threshold`: threshold form (min over S of p-eps > t >= max over complement of p+eps), which is the min/max statement without a Finset min.
- `steering_gain_not_learning_value`: witness G th = th, V th = th*th, 0 -> 1: G rises and V rises.
- `sample_residual_not_uniform`: for every finite list S there are f, g agreeing on S and differing somewhere.
- `dot_self_nonneg`, `dot_comb`, `cauchy_schwarz`: (dot x y)^2 <= dot x x * dot y y over Int.
- `squared_l2_functional_bound`: dot c u ^2 <= B whenever dot c c * dot u u <= B (squared-l2 admission form, derived from Cauchy-Schwarz).

## Build
`lake build` tail: `Build completed successfully (134 jobs).`
`lake env leanchecker MathCan.SCCG10Admission`: exit code 0, no output.

## `#print axioms`
    'dot' depends on axioms: [propext]
    'stale_target_lower' depends on axioms: [propext, Quot.sound]
    'stale_protected_linf' depends on axioms: [propext, Quot.sound]
    'refresh_value_le_gap' depends on axioms: [propext, Quot.sound]
    'ranking_certificate' depends on axioms: [propext, Quot.sound]
    'ranking_topset' depends on axioms: [propext, Quot.sound]
    'ranking_topset_threshold' depends on axioms: [propext, Quot.sound]
    'steering_gain_not_learning_value' does not depend on any axioms
    'sample_residual_not_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
    'dot_self_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
    'dot_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
    'cauchy_schwarz' depends on axioms: [propext, Classical.choice, Quot.sound]
    'squared_l2_functional_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

Only propext, Classical.choice, Quot.sound appear. No `sorry`, no new `axiom`.

## Not formalized
- Real-valued l2 norms and the real Cauchy-Schwarz dual upper bound (only the integer squared form above).
- Any statement about native transformer outputs, learned models, or that the hypotheses hold for a real checkpoint.
- Whether a given declared span, dose bound, or residual bound is true of an actual run.
