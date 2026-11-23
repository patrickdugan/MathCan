# RH-26E-01 pre-registered scalar-transport Lean gym

**Registration:** 2026-11-23, source only, before implementation or CI.  
**Mathematical origin:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean`: `StepBeta` lines 597–605 and `StepAlpha` lines 608–617, as isolated in [RH26B03_ORIGINAL_PREMISES.md](RH26B03_ORIGINAL_PREMISES.md).

## Question

Can a fresh, independent Lean 4.35 CPU module verify the elementary nonvanishing consequences of the alpha/beta theta-integral transport equations, while explicit adversarial examples demonstrate each indispensable nonzero/invertibility premise?

This experiment checks an algebraic **toy cut**, not Alpöge's automorphic proof, a multiplicity estimate, a theta-integral normalization, a spectral theorem, or RH/GRH.

## Registered exact formal targets

Field-general over `α` with `[Field α]` (hence specializing to `ℂ`):

1. **BETA-NORMALIZED:** from `u*d=1` and `c*l=u*c₁`, derive `c₁=d*c*l`.
2. **BETA-NONZERO:** with the same hypotheses and `c₁ ≠ 0`, derive `l ≠ 0`.
3. **ALPHA-NONZERO:** from `c=d*l*c₁` and `c ≠ 0`, derive `l ≠ 0`.
4. **CONTROLS:** prove explicit counterexample instances over `ℂ` (or any suitable field) of the beta equations with `c₁=0, l=0` and `u*d=1`; of beta's relation with `c₁ ≠0, l=0` after removing `u*d=1`; and of alpha's relation with `c=0,l=0` after removing `c≠0`. These are *positive proofs of existence*, not failed build jobs.

The theorem names will be `RH26E01.beta_normalized`, `RH26E01.beta_nonzero`, `RH26E01.alpha_nonzero`, `RH26E01.beta_no_target_counterexample`, `RH26E01.beta_no_inverse_counterexample`, `RH26E01.alpha_no_source_counterexample`.

## Null and falsifier

The null hypothesis is that at least one deduction needs an unregistered hypothesis, or the Lean declarations incorrectly abstract the original rank-step identities. A failure to compile, unexpected axioms or admissions, a missing required counterexample, or mismatch with the exact pinned equations is a FAIL. A green compiled field lemma alone supports **only** the declared field-level conclusion.

## Scope and acceptance

- Store original source in `research/rh26/lean/RH26E01ScalarTransport.lean`; store CI receipt and run report in `research/rh26/RH26E01_RESULTS.md` and `LEDGER.md`. Keep this folder isolated from the upstream unlicensed proof code.
- Use `experiments/deligne_mathlib` as the repository's existing pinned Lean 4.35.0 + Mathlib v4.35.0 environment, without changing its manifest, source, default target or root toolchain.
- CPU-only GitHub-hosted Actions, maximum 25-minute job. Fetch Mathlib cache, typecheck **only the RH26E01 file** with `lake env lean`. Explicitly avoid `lake build Deligne04` and any pretrained model, GPU, QPU, or paid pod.
- `#print axioms` of each of six declarations; reject `sorryAx`, `ofReduceBool`, custom or opaque axioms. A typechecked file plus permitted foundational axiom output is PASS, provided the control declarations compile. If CI is unavailable, record UNVERIFIED.
- Exact pinned upstream and MathCan commit SHAs, GitHub Actions run link, compiler version and the complete axiom receipt are required before claiming KERNEL PASS.
- Distinguish CI PASS from interpretation. Underlying `StepAlpha`/`StepBeta`, `OneConst` and `IsMatched` remain **upstream premises**, and no independent reconstruction of their mathematical content is being attempted here.

## Allowed next steps

1. Commit this registration before writing the Lean and workflow source.
2. Implement and commit six targets. Run CPU CI on the research branch; audit and repair any failures before recording success.
3. Commit a report and append a concise restart entry to `LEDGER.md`. Draft PR #265 remains unmerged.
4. The follow-on RH-26B-04 should seek exact proof suppliers of rank-step transport under a separate source-only registration.
