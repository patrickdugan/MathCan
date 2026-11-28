# SCCG-10 / MMS-TRM economics and transport: Lean receipt

Module: `MathCan/MMSTRMEconomics.lean` (imported from `MathCan.lean`). Core Lean only,
toolchain v4.35.0, no Mathlib. Integers stand in for exactly scaled rationals.
Companion to BPD `mechinterp/bpd/experiments/sccg10_native_mms/MATH_REVIEW.md`
(branch research/sccg10-mms-trm-20261127). Extends `SCCG10Admission.lean`.

## Theorems
- `voi_refresh_le` (Prop. 9): stale-score argmax loses at most 2*delta + 2*eps against
  the fresh-score argmax when |s - s_fresh| <= delta and |s_fresh - r| <= eps pointwise.
- `voi_refresh_sharp`: explicit two-candidate witness attaining equality.
- `chrono_prod_bound` (Prop. 3, scalar case): for paired lists of per-step factors,
  |prod a' - prod a| <= prod(|a| + |a' - a|) - prod |a|, by induction on the list.
- `chrono_prod_sharp`: aligned nonnegative perturbations attain the bound.
- `ratio_rule` (Prop. 14): with v2*c1 <= v1*c2, v1 >= 0, n2 >= 0 and n1*c1 + n2*c2 <= B,
  (n1*v1 + n2*v2)*c1 <= B*v1.
- `near_null_persistence` (Prop. 4a): |c'u| <= |cu| + |(c'-c)u|.
- `myopic_not_two_step` (Prop. 10c): one-step greedy choice loses over two windows.
- `refuse_audit`: gain <= voi <= cost*rate gives gain - cost*rate <= 0.

## Build
`lake build MathCan.MMSTRMEconomics`: `Build completed successfully (2 jobs).`
`lake env leanchecker MathCan.MMSTRMEconomics`: exit code 0, no output.
`grep -c sorry MathCan/MMSTRMEconomics.lean`: 0.

## `#print axioms`
    'MathCan.MMSTRMEconomics.voi_refresh_le' depends on axioms: [propext, Quot.sound]
    'MathCan.MMSTRMEconomics.voi_refresh_sharp' does not depend on any axioms
    'MathCan.MMSTRMEconomics.chrono_prod_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
    'MathCan.MMSTRMEconomics.chrono_prod_sharp' does not depend on any axioms
    'MathCan.MMSTRMEconomics.ratio_rule' depends on axioms: [propext, Quot.sound]
    'MathCan.MMSTRMEconomics.near_null_persistence' depends on axioms: [propext, Quot.sound]
    'MathCan.MMSTRMEconomics.myopic_not_two_step' does not depend on any axioms
    'MathCan.MMSTRMEconomics.refuse_audit' depends on axioms: [propext, Quot.sound]

Only propext, Classical.choice and Quot.sound appear. No sorry, no new axiom.

## Not formalized
- Matrix/operator-norm version of the chronological bound (only scalar factors).
- Real-valued norms, the Wedin/kernel-angle bound (Prop. 4b), metric equivalence (Prop. 5),
  gauge counterexample (Prop. 6), and the alignment condition of Prop. 11.
- Any claim that the hypotheses hold for a trained ComponentTRM checkpoint.
