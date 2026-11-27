# RHD-COMP-01: compact RH proof as a second source ledger

Date: 2026-11-27. Status: **source inspection; external verification evidence; no independent new Lean proof**.

Existing RHD-01–16 files refer to the original source at `leanprover-community/riemann-hypothesis@f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`. Retain that pin and its compiled references. This note adds the later readable/compact rewrites as separate sources, never substitutes their declarations for old ones by name alone.

- Compact/readable upstream: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
- Compact entrypoint: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Main.lean
- Compact guide: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/GUIDE.md
- Independent verification: https://math.mit.edu/~drew/shortgrh/
- Original formal certification: https://leanprover-community.github.io/blog/posts/riemann-hypothesis/
- Minimal packaging: https://github.com/1337isnot1337/riemann-hypothesis-minimal

Both shorter versions use Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. Sutherland reports identical challenge statements across the two rewrites, only the standard three axioms, and successful independent replay. The original uses a different Mathlib revision; the report explicitly says formal equivalence of the original and later Mathlib versions has not been checked. Do not erase that caveat.

## Source anchors for the next mathematics review

| Compact file | Interface | Role |
|---|---|---|
| src/New/Endgame/ShortAndEnough.lean | Data.short_forms / Data.enough_forms | Upper norm and near-spanning witnesses |
| src/New/Endgame/LongForms.lean | Data.integral_forms_long / Data.exists_family_covolumeSq_le | Lower/upper volume bounds |
| src/New/Data/DataExist.lean | exists_data | Admissible data at large x |
| src/New/Endgame/OneSidedCriterion.lean | IsPolar.exists_window_sub_mul_le / entireL_ne_zero_of_primeError_le | Window selection and zero exclusion |
| src/New/Selmer/FitTwistsExist.lean | exists_isFitFamily | Congruence-controlled twists |
| src/New/Rows/RowVolume.lean | volume_iota_eq_prod_liftVolume | Multiplicative volume decomposition |
| src/New/Rows/LiftVolumeHeight.lean | heightLe_liftVolume_ratio | Height bound on twisted lifts |
| src/New/Main.lean | star_inequality / eventually_primeError_le_rpow / New.grh | Endgame |

Source algebra: put d=rowDim, L=logB*budget, h=mainHeight-m*remainder+L. The lower and upper bounds give

    d*(mainHeight - 3*L) <=
      d*(mainHeight-m*remainder+L+4*x^99+10*log(1+b^2)*budget).

For d>0, subtract the common height and divide by d:

    m*remainder <= 4*L + 4*x^99 + 10*log(1+b^2)*budget.

The compact source then uses admissible-scale bounds to obtain m*remainder <= logB^2*budget, with budget=f*a*logB^3. Combined with the second-scale window estimate and m >= sqrt(x), this gives an eventual one-sided bound primeError <= x^(8*epsilon - 1/2). Landau-type exclusion plus the functional equation yields the five stated theorems. These deductions summarize inspected source; they do not establish that every geometric hypothesis in the original RHD line is equivalent to the compact reformulation.

## Next gates

- Match old RHD witness obligations to compact types using separately hashed source + compiled reference graphs; classify exact type match, provable bridge, plausible analog, absent. Require explicit Lean bridge for equivalence. In particular do not identify the old character extension interfaces with FitTwists merely because both concern twists.
- Extract a self-contained exact scalar cancellation lemma with positive dimension and explicit error hypotheses; use the existing MathCan style, test sign reversal/zero-dimension/failure controls, and keep geometric assumptions explicit.
- Compare readable and compact New.Variety.tiltTheory at the declaration/type level and isolate reduction/conversion cost on independently checked minimal roots. The former reportedly took 7917635 ms in lean4lean, but checker-specific bottleneck and many upstream changes confound attribution.
- Independent foundational route: investigate available set-theory translations and Metamath representations; distinguish replay by existing independently implemented checkers from a new Metamath proof. No successful translation is claimed.

See MoralityLabAI/Compactification-Theory, branch research/rh-proof-compactification-20261127, for the source DAG analyzer and preregistration. Treat the public RH corpus as already exposed.
