# RH-26E-03: independent density-normalized scalar growth bound

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26E03_REGISTRATION.md](RH26E03_REGISTRATION.md), `e8dd41174d9a6ff1f2d201261b4ddb64b2d45120`, before executable source.  
**Implementation:** [RH26E03GrowthBound.lean](lean/RH26E03GrowthBound.lean), initially `71c25b03`, explicit power regrouping at `b4d3b5c7`, workflow commit `108f74fdb2305889c04bd02c02827c76ce711a30`.  
**Disposition:** IMPLEMENTED; **KERNEL RESULT PENDING**. Source inspection found all fourteen preregistered theorem declarations with matching axiom-report commands and no sorry/admit tokens. This does not establish successful elaboration or a kernel pass.

## Mathematical scope

The module independently encodes the source's real scalar window (generalized from natural cardinalities by coercion), raw error bracket B, per-slot normalization, and the actual density-corrected scalar input. It imports Mathlib only. The exact motivating source boundaries and independent derivations are in [RH26C02_ERROR_BRACKET.md](RH26C02_ERROR_BRACKET.md) and [RH26C03_NORMALIZATION.md](RH26C03_NORMALIZATION.md), at the frozen upstream pin `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.

The intended scalar conclusion, with Q=Nmb, delta=P/n, R=B/Q, is:

```text
Window x eps n N P m b k a, C>=0,
Err<=x^(C*eps)*B,
Q*(delta/2)*(G-4*x^(1/2+eps))<=Err+2*Q/x
  => G<=x^(1/2+(C+3)*eps).
```

The positive denominator facts follow from Window. The final proof uses the 10Y bound for R with Y=x^(1/2+13eps/8), the inverse density cost 1/delta<=x^eps, and Z=x^(1/2+(C+21/8)eps). The normalized contributions are <=20Z, <=2Z and <=4Z; 26<=x^(3eps/8) yields the desired exponent. The observable G remains signed. All real-power relationships must be proved; no power-scale axioms are declared.

## Frozen checks

| Declarations | Target |
| --- | --- |
| window_positive, bracket_normalization, card_ratio | Positive denominators, exact bracket division, finite-cardinality loss |
| component_bounds, bracket_bound | Four terms with coefficients 2,2,4,2 and constant-10 envelope |
| two_term_envelope | Power-loss upper envelope under m>=1, which holds for the positive natural source m |
| density_inverse, density_normalize | Exact inverse-density cost and both additive remainders |
| growth_bound | Full real-power scalar conclusion with C>=0 and actual Err inequality |
| zero_density_control, zero_volume_control | Concrete degenerate coefficients admitting arbitrary large signed G |
| missing_density_control | Positive Q,delta,x example violates a normalization with the inverse-density cost removed |
| no_loss_family, no_uniform_no_loss | Integer t scalar family with eps=1, x=t², m=b=t, n=N=P=x, k=a=x*t, eventual threshold and failure of any uniform fixed positive A,D envelope |

The counterexample concerns the **normalized bracket**, not the actual potentially smaller gap or a realized arithmetic host. The source scalar lower/upper bounds on m remain constraints on a valid family, not evidence that the user can freely choose its minimizer.

## Verification receipt (pending)

- CPU run [45279143901](https://github.com/patrickdugan/MathCan/actions/runs/45279143901), job `138058675275`, source/workflow commit `108f74fdb2305889c04bd02c02827c76ce711a30`.
- Source blob `5cc2de37912655520a65901ea75761d85951334d`; 437 lines, 14 theorem declarations and corresponding print-axioms names.
- Last check: checkout, pinned toolchain validation and Lean setup succeeded; Mathlib resolution in progress, kernel step pending.
- One isolated GitHub CPU job, 25-minute cap, Lean 4.35.0 and Mathlib v4.35.0. Require exact registered axiom names and only propext, Classical.choice, Quot.sound. Source SHA-256, actual dependency pin, elapsed time/RSS, and audit artifact are pending.

No full upstream/Deligne build, GPU, QPU, or paid cloud requested. If the job fails, preserve the errors and repair within the frozen contracts. If green, update this report with literal audit results and close the ledger gate. No independent RH or analytic proof claim.

## Next research boundary

Check the exact CPU run before proceeding. After closing this verification, revisit RH-26D (operator/arithmetic holonomy bridge) or the unresolved RH-26B quantitative multiplicity theorem. A separately preregistered RH-26C-04 may locate the exact upstream proposition_size_bound assembly after line 250 of LipschitzWeightAndMinimum.lean. Retain the pinned source and bounded read rules.
