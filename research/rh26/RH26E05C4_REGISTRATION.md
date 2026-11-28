# RH-26E-05C4 registration: unified scalar export

Date: 2026-11-24 (Asia/Manila). Host: draft PR #265. Parent 86d29f74bc051d7eee7f44e25ce94402e099d889. Freeze before implementation. Source anchors: B10, B12, B13, B14 at upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. No new upstream reads in this experiment.

## Contracts

Import C1, C2, C3 as distinct compiled Lean modules; preserve the 15+12+18 existing declarations and audit them again. Their negative controls and optimality statements are audited as independent declarations, not artificially inserted as dependencies of the positive theorem.

Let S be a finite set of natural prime labels, A1..A5 raw eligibility masks, T_i = S filtered by membership in A_i. Costs v_i are log-weighted, nonnegative on S. Priority is generator, small/3, ramified, generic small, exceptional, then zero. The masks can overlap. For the arithmetic source, generic cutoff and exceptional-large masks are disjoint, and large nonexceptional primes have zero generic cost. Do not infer source compatibility of arbitrary masks.

Freeze these new public names in RH26E05C4:
- priority_le_masks: the priority-selected cost is bounded by the sum of five individually masked nonnegative costs, including no-active-mask zero.
- sum_mask: equality between the masked sum and filtered sum.
- five_mask_majorant: the finite selected sum is bounded by the five filtered sums, plus the same additive correction.
- exceptional_local: use the mixed denominator, exact cutoff ratio, division, eP, flat, bb, split/inert bounds and pointwise assembly to derive the 95 envelope under explicit C3 premises. Preserve the split/inert disjunction; nonnegative factors and denominator constraints are premises.
- exceptional_filtered: derive the 58 cardinality and 11020 weighted sum from the mixed count premises and pointwise caps, applying C3 count_mixed_bound, count_envelope and exceptional_sum.
- unified_point_bound: on the same S and masks, set X=fm*b*g², derive the small/3 sum from C2.row23_assembly and the ramified sum from C2.ramified_assembly, the generic small sum from C2.small_assembly and its six scalar suppliers, the exceptional sum from exceptional_filtered. Generator and global correction keep original bounds. Apply the five-mask majorant and C1.refined_assembly to obtain Y <= 105(C+1)^3 X whenever Y is below the selected sum plus correction. Retain C>=0, H>=2, fm>=1, g>=1, b>=1, scale and all arithmetic supplier premises. The pointwise exceptional cap can be supplied via exceptional_local; no implied host realization.
- unified_export: consume unified_point_bound (or its exact conclusion) and C1.export_propagation to obtain eta <= R*(105(C+1)^3*(X+N)+V) with R,N>=0.
- overlap_control: concrete 2+3 overlap gives selected 2 and masked 5; an inactive branch returns zero; negative omitted cost fails majorization.

Acceptance: audit all 45 prior plus 8 new names individually, compile C1/C2/C3 to oleans and C4 importing them, exact axiom allowlist propext/Classical.choice/Quot.sound, no sorry/admit/native_decide, no custom axioms, no upstream imports. CPU-only isolated Lean v4.35.0 / Mathlib v4.35.0 workflow, 25 minute cap; preserve source hashes, dependency/compiler identity, timing/RSS and logs. Report actual run status; no upstream point_bound/aux3 replacement or global RH exponent claim. B15 N.linkN_of remains separate.
