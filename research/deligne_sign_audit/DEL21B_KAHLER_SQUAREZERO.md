# DEL-21B: Kähler differentials, derivations, and square-zero algebra lifts

**Date:** 22 November 2026.
**Parent:** [DEL-21 issue #212](https://github.com/patrickdugan/MathCan/issues/212).
**Predecessor:** [merged DEL-21A PR #215](https://github.com/patrickdugan/MathCan/pull/215).

## Formal bridge already available in Mathlib

The pinned Mathlib 4.35 implementation contains two compatible universal properties:

    Hom_A(Ω[A/R],M) ≃ Der_R(A,M)

through KaehlerDifferential.linearMapEquivDerivation, and

    Der_R(A,I) ≃ {f:A→ₐ[R] B | f mod I = canonical map}

through derivationToSquareZeroEquivLift, for any algebra tower R→A→B and ideal I⊂B with I²=0.

The new Lean theorem kahlerSquareZeroLiftEquiv composes these exact equivalences, retaining their dependent typeclass requirements. The target is an algebra-homomorphism lift, which makes the base-algebra structure explicit. The result is valid over arbitrary commutative base rings and does not presume that a variety is smooth.

## Dual numbers at a K-rational point

Mathlib's TrivSqZeroExt.kerIdeal K K is the actual square-zero ideal of the dual-number algebra DualNumber K. Its square-zero theorem is a kernel-verified Mathlib fact in all characteristics.

Given a K-rational point point:A→ₐ[K]K, DEL-21B constructs the constant lift A→ₐ[K]DualNumber K by composing point with the coefficient inclusion. It proves that projection to the scalar component recovers point and constructs the point-induced A-algebra structure on DualNumber K.

The specialization kahlerDualNumberLiftAtPoint identifies A-linear functionals on Ω[A/K] valued in the dual-number nilpotent ideal with all A→DualNumber K lifts of the corresponding constant map through its square-zero quotient. This is the algebraic dual-number tangent-to-Kähler bridge at a specified point.

## Exact independent audit

Ninety-six frozen finite-field cases across F2, F3, F5, F7, F11, F13, F17 check the Kähler cotangent fiber via the Jacobian conormal presentation, then enumerate matching first-order dual-number lifts.

Examples: smooth parabola y=x², node xy=0 at the origin, nonreduced double line x²=0, reduced line x=0, double root (x-a)², and simple root x-a. The oracle checks the expected number p^dim of tangent directions for each Kähler-fiber dimension, preservation of redundant ideal generators, and characteristic-two behavior.

The double line and its reduction have equal rational zero sets and different first-order tangents, so the full quotient ideal is retained.

## Remaining DEL-21 geometry

The DEL-21B correspondence applies to the K-algebra A of the genuine quotient coordinate ring, once its K-rational point u is supplied through the quotient. The subsequent natural-coordinate identification with DEL-21A's concrete polynomial Jacobian tangent and the Kähler base-changed fiber Ω[A/K]⊗_A K is a separate explicit Lean target. Mathlib also has the cotangent complex sequence and coordinate-basis derivatives in RingTheory/Extension/Cotangent/Basic.lean.

The project-wide general Bertini incidence closure/properness proof and effective parameter degrees remain open, with Katz weak Lefschetz requiring a separate good-locus theorem.

**Acceptance:** pinned Mathlib 4.35 Lean kernel and axiom audit, exact 96-case oracle, full MathCan compatibility suite.
