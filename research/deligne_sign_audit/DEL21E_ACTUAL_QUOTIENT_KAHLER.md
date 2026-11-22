# DEL-21E: genuine quotient algebra presentation and Kähler differentials for U^k

**Date:** November 22, 2026.
**Parent:** [DEL-21 issue #212](https://github.com/patrickdugan/MathCan/issues/212).
**Predecessor:** [DEL-21D PR #224](https://github.com/patrickdugan/MathCan/pull/224), merged at 46ab96f.

## Actual quotient coordinate ring

For a field K and a finite affine closed-embedding presentation U=V(f_j), the actual k-fold product has ambient polynomial ring

    P = MvPolynomial (Fin k × Fin s) K

and full defining ideal

    I = Ideal.span (Set.range (Deligne16.copyEquation f)).

DEL-21E defines the true quotient coordinate ring A=P/I. It then constructs an Algebra.Presentation K A (Fin k × Fin s) (Fin k × Fin r) whose generators map each coordinate to its residue class and whose relations are precisely the original lifted equations. It proves the presentation relation span is the actual kernel of the canonical quotient algebra map.

This keeps the complete ideal I rather than its radical. Redundant relations remain valid and nonreduced schemes are retained.

## Genuine Kähler module

Mathlib 4.35 provides Algebra.Presentation.differentials, a formal Module.Presentation A Ω[A⁄K] built from the universal conormal exact sequence. DEL-21E invokes this construction on the actual U^k quotient-algebra presentation, giving the genuine Kähler module with exactly the original coordinate and relation index sets.

The explicit module-presentation relation coefficient is the image in A of the original polynomial partial derivative of the lifted relation. In DEL-21C, the same partials were already kernel-checked as coordinates of the universal differential in the free polynomial Kähler module.

## Independent tests

The standard-library Python oracle replays DEL-21D's 160 actual finite-field cases, checking the index counts, the full set of derivative rows, the product-factor relation independence, and quotient-rank counts. The double-line x²=0 retains all tangent directions at x=0, while the reduced x=0 quotient has a rank-one conormal row. The redundant (x²,x³) relations preserve the original tangent. Characteristic-two derivatives are audited.

## Next quotient-fiber naturality theorem

The final bridge is a canonical K-linear equivalence

    Ω[A/K]⊗_A K ≃ₗ[K] (K^(ks) / R_u)

where u:A→K is the chosen rational point and R_u is DEL-21D's actual evaluated Jacobian-row span. Obtain it by base changing the proved module presentation A Ω[A/K] along u, then use the pinned Mathlib module-presentation exact sequence and the finite polynomial differential-basis theorem to identify the row-span presentation.

Composing this with DEL-21D will prove

    Dual_K(Ω[A/K]⊗_A K) ≃ₗ[K] jacobianTangent(f,u).

This quotient-fiber identification, including explicit scalar tower, base-change naturality, and geometric field extensions, is outstanding until separately kernel checked. It must preserve nonreduced ideals. Bertini incidence properness, effective degrees and Katz weak Lefschetz remain separate.

**Acceptance:** pinned Mathlib 4.35 Lean kernel and axiom audit, exact independent oracle and complete MathCan compatibility checks.
