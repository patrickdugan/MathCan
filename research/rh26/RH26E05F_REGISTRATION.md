# RH-26E-05F registration: support-preserving valuation export

**Date:** 2026-11-24 (Asia/Manila). Frozen before executable proof and CI.
**Host:** MathCan draft PR #265, research/rh26-extraction-rubrics-20261123.
**Inspiration:** B14 exact source trace of MemPrimesOverOfMem.lean:606–695 and ExportBoundOfAdmissible.lean:1066–1096, frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. No new upstream reads/imports. Independent of E05C1's pending repair audit; may use the original 2000 coefficient or a supplied coefficient K.

## Question

Recover the finite-support upper certificate prior to summability, using the actual source's two residual sum inequalities and its five-component prime-wise cost (signature split into inverse-square and nu contributions). Track the two units of numerical padding, the cohomological tail, and the nonnegative Nc-style padding as exact discarded-envelope terms. Preserve arbitrary real cohomological values in finite algebra; monotone extension to an infinite total needs nonnegative summable values.

For finite S:Finset I, use real arrays eta,e,nu,lam,vv,h,g representing already log-weighted quantities. Per-index upper premise eta_i<=R*(2e_i+nu_i+lam_i+vv_i+h_i+g_i); R>=0. Source bounds sum_S e<=2, sum_S nu<=Bnu, sum_S h<=Bh, sum_S g<=Bg. Define source point allowance P=6+Bnu+Bh+Bg+sum_S lam. A supplied upper bound P<=KX is the actual point_bound contract, with K=2000(C+1)^3 or another independently certified coefficient. N represents the nonnegative padding (log x)^2 Nc. The arithmetic identification of all arrays remains external.

## Twelve frozen public theorem contracts (RH26E05F namespace)

1. finite_aggregation: sum_S eta<=R*sum_S (2e+nu+lam+vv+h+g) from the per-index inequality.
2. signature_budget: sum_S e<=2, sum_S nu<=Bnu imply sum_S (2e+nu)<=4+Bnu, with no sign restrictions on these arrays.
3. finite_support_bound: per-index and four component sum premises, R>=0, imply sum_S eta<=R*(4+Bnu+Bh+Bg+sum_S lam+sum_S vv), no summability premise.
4. finite_export: under the same premises and 6+Bnu+Bh+Bg+sum_S lam<=KX, obtain sum_S eta<=R*(KX-2+sum_S vv), without summability.
5. nonnegative_tail: for v:I→ℝ, Summable v and v_i>=0, define tail=tsum v - sum_S v; prove tail>=0.
6. tail_identity: for arbitrary real v and finite S, total tsum v=sum_S v+tail; algebraic identity, meaningful analytic interpretation under summability.
7. padding_slack_identity: R*(K*(X+N)+V)-R*(KX-2+F)=R*(2+(V-F)+KN) for arbitrary real scalar parameters.
8. padding_slack_nonneg: R,K,N>=0, Summable v and v>=0 imply the old padded infinite envelope exceeds or equals the support-preserving envelope; also prove the exact slack formula with tail.
9. combined_export: under finite_export premises plus Summable vv, nonnegative vv, K,N>=0, conclude both finite-support bound and the padded infinite upper bound sum_S eta<=R*(K(X+N)+tsum vv).
10. nonnegative_tail_fixture: Fin 2 values (2,3), support {0}: sum=2, tsum=5, tail=3; exact finite-type evaluation.
11. signed_tail_control: Fin 2 values (2,-3), support {0}: sum=2, tsum=-1, tail=-3; summable but finite sum exceeds total.
12. nonsummable_support_control: constant-one real sequence on Nat is not summable, every finite support has sum equal to its cardinality, and in particular a singleton sum is 1. Prove non-summability using nonnegative finite partial-sum bounds and unbounded cardinalities or an equivalent native Mathlib argument.

## Acceptance

All twelve registered names typecheck and pass the exact theorem-level axiom allowlist (propext, Classical.choice, Quot.sound) on Lean 4.35.0 / Mathlib v4.35.0. No sorry/admit/native_decide/custom axioms. Preserve failed receipts and repair within frozen theorem types. Isolated source research/rh26/lean/RH26E05FSupportExport.lean and CPU workflow using existing experiments/deligne_mathlib pin, 25-minute timeout. Record source/compiler/dependency hashes, elapsed/RSS and audit artifact. No full upstream/Deligne build, GPU/QPU or paid compute. This proves independent finite and analytic-tail consequences under supplied hypotheses, not existence of a nonsummable arithmetic family or a stronger upstream RH theorem.

Deliverables: results report, ledger, inventory and draft PR checkpoint. Next E05B degree-weighted rank certificate or remaining E05C supplier proofs; B15 source inventory remains queued.
