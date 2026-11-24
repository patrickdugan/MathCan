# RH-26E-05F: finite-support valuation export and padding slack

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26E05F_REGISTRATION.md](RH26E05F_REGISTRATION.md), `16338cea2b60d3336c44a9c1daaaf8370aa9bcae` before executable proof and CI.  
**Implementation:** [RH26E05FSupportExport.lean](lean/RH26E05FSupportExport.lean), `8a9ca88d32b2766e45d4bac00b289be98fa40780`; source and workflow `d5b29a3aca8d1727c961c0a9ab73438929e6869f`.  
**Disposition:** IMPLEMENTED; **KERNEL RESULT PENDING**. Twelve theorem declarations and matching axiom-print names inspected. No admission or native_decide tokens. The previous independent E05C1 audit passed 15/15 during this session.

## Source contract and scope

[B14](RH26B14_AUX3_EXPORT.md) recovers the exact finite support step of MemPrimesOverOfMem.lean:606–695 and the export_bound_of_admissible proof at ExportBoundOfAdmissible.lean:1066–1096, frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. All source-specific arithmetic and rank hypotheses enter the independent module as supplied scalar and finite-sum premises. No upstream proof imports or new source reads.

Let S be the finite prime support, R>=0 the rank, and e,nu,lam,vv,h,g the already log-weighted arrays. The per-index bound eta_i<=R*(2e_i+nu_i+lam_i+vv_i+h_i+g_i) yields the finite aggregation. With sum e<=2, sum nu<=Bnu, sum h<=Bh, sum g<=Bg, the signature term is bounded by 4+Bnu. No sign hypothesis on the individual arrays is required for those additive steps. The actual point allowance P=6+Bnu+Bh+Bg+sum lam<=KX implies the independent finite result

```text
sum_S eta <= R*(KX-2+sum_S vv).
```

Here K may be the original coefficient 2000(C+1)^3 or another separately certified coefficient. The theorem does not assume Summable vv. The source's identification of these arrays and admissible-table existence remain external.

For a real-valued array v on arbitrary index type, define Tail(S)=tsum v-sum_S v. Under Summable v and nonnegative v, this tail is nonnegative. The exact difference between padded infinite and finite envelopes is

```text
R*(K*(X+N)+tsum v) - R*(KX-2+sum_S v)
 = R*(2+Tail(S)+K*N).
```

Nonnegative R,K,N certify that the padded envelope is at least the finite one. N represents the source term (log x)^2 Nc. This establishes a conditional scalar export refinement, not an improved asymptotic exponent or an arithmetic family with nonsummable cohomology.

## Twelve frozen declarations

| Name | Contract |
| --- | --- |
| finite_aggregation | Sum pointwise upper bounds over finite support |
| signature_budget | Four-unit signature budget |
| finite_support_bound | Finite support upper bound before use of summability |
| finite_export | Preserve the two-unit numerical slack |
| nonnegative_tail | Monotone extension for nonnegative summable arrays |
| tail_identity | Algebraic finite-plus-tail decomposition |
| padding_slack_identity | Exact difference of two scalar envelopes |
| padding_slack_nonneg | Exact difference and order under nonnegative premises |
| combined_export | Both finite and padded infinite estimates |
| nonnegative_tail_fixture | Fin 2 values 2,3, support {0}: finite 2, total 5, tail 3 |
| signed_tail_control | Fin 2 values 2,-3: finite 2, total -1, tail -3, summable |
| nonsummable_support_control | Constant-one Nat sequence is nonsummable with finite sums equal to cardinalities |

The finite-sum argument for nonsummability uses arbitrarily large finite cardinalities and the upper bound by the tsum that would follow from summability and nonnegativity. The signed example isolates the need for the nonnegative omitted values premise. R=0 annihilates the exact slack formula.

## Verification receipt (pending)

- [Run 45337671069](https://github.com/patrickdugan/MathCan/actions/runs/45337671069), job 138253495876, checked `d5b29a3aca8d1727c961c0a9ab73438929e6869f`.
- Source blob `a718b6cbb6ffbef28264c938e686053f4c655caf`, 159 lines. Twelve exact names match the audit print commands. Checkout and registration/pin checks passed; Lean installation in progress at latest observation.
- Require successful compiler exit, exact twelve-name allowlist audit with only propext/Classical.choice/Quot.sound, source SHA-256, compiler and Mathlib pins, elapsed/RSS, artifact.
- Isolated CPU Lean 4.35.0 / Mathlib v4.35.0 job, 25-minute cap. No full upstream/Deligne build, GPU/QPU or paid compute.

Inspect this exact run first on resumption and retain failures before proof-only repairs. Then prioritize E05B degree-weighted rank/capacity certificate, independent stronger E05C suppliers, or B15 source inventory of N.linkN_of. E05C1 15/15 final audit is separately recorded in its own report.
