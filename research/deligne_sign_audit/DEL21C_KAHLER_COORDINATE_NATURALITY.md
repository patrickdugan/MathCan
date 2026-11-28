# DEL-21C: naturality of the polynomial Kähler basis and quotient dual-number tangents

**Date:** 22 November 2026.
**Parent:** [DEL-21 issue #212](https://github.com/patrickdugan/MathCan/issues/212).
**Predecessors:** merged [DEL-21A #215](https://github.com/patrickdugan/MathCan/pull/215) and [DEL-21B #218](https://github.com/patrickdugan/MathCan/pull/218).

## Universal differential in actual polynomial coordinates

Let P=K[z_i] be an actual finite Mathlib MvPolynomial ring, let u be a point and v a tangent-coordinate vector. Mathlib 4.35 constructs the genuine basis of its Kähler module Ω[P/K] consisting of d(z_i), with coordinate formula:

    (mvPolynomialBasis K σ).repr (D K P Q) i = pderiv_i Q.

DEL-21C defines the scalar **coordinate readout** on Ω[P/K] by evaluating those actual basis coefficients at u and pairing them with v:

    readout_(u,v)(ω) =
      Σ_i eval_u ((mvPolynomialBasis K σ).repr ω i) * v_i.

Its kernel-checked theorem kahler_readout_D_eq_directional proves for every polynomial Q:

    readout_(u,v)(dQ) = Σ_i eval_u (pderiv_i Q) v_i.

The right side is DEL-21A's exact tangentDerivative, so firstOrder_snd_eq_kahler_readout proves

    snd (firstOrderEvaluation u v Q) = readout_(u,v)(dQ).

The coordinate theorem reduces to readout_(u,v)(d z_j)=v_j. This confirms the abstract universal Kähler construction in the explicit actual coordinate basis, including characteristic two.

## Natural compatibility with the actual quotient ring

Let I be any ideal of P, and let F:(P/I)→DualNumber K be a ring homomorphism whose composition with the quotient map equals DEL-21A's firstOrderEvaluation u v.

The theorem quotient_firstOrder_snd_eq_kahler_readout proves for every Q in P that

    snd(F([Q])) = readout_(u,v)(dQ).

It also proves the identity F([z_i])=(u_i,v_i) for each coordinate. This covers nilpotent defining ideals because F must factor through the actual quotient; a pointwise or radical-only replacement would change the allowed first-order directions.

The specialized theorem product_tangent_exists_kahler_natural_lift takes a tangent vector from DEL-20's Jacobian-kernel subspace of the actual DEL-16 embedded product U^k, obtains its quotient dual-number lift from DEL-21A, and certifies this coordinate compatibility in the chosen presentation.

## Independent verification

The 144-case deterministic prime-field corpus covers F2, F3, F5, F7, F11, F13, F17. It implements independent exact sparse-polynomial formal partials and dual-number substitution of nonlinear polynomials through bidegree (2,2) and y-degree three. Categories include smooth parabola, node, double line, radical mutation, redundant generators, and generic polynomials.

The tests check the product rule, equality of the epsilon coefficient and actual differential-coordinate pairing, naturality through ideal multiplication, nonreduced-vs-reduced mutations, and characteristic-two power rules.

Lean module: experiments/deligne_mathlib/Deligne04/KahlerCoordinateNaturality.lean
Corpus: research/deligne_sign_audit/del21c_tasks.jsonl
Exact tests: tests/test_deligne21c_kahler_naturality.py

## Boundary of the formal result

This module proves the coordinate comparison in the **free polynomial Kähler module**, along with its naturality under a dual-number map that factors through a quotient. The remaining statement is a canonical linear equivalence on the quotient's base-changed Kähler fiber:

    Hom_K(Ω[(P/I)/K] ⊗_(P/I) K, K)
       ≃ₗ[K] jacobianTangent_I(u).

The proof must explicitly construct the point-induced algebra/module structures and tensor base change, identify the cotangent complex differential with the true pderiv Jacobian, and prove all maps commute with quotient projection. The local smoothness condition, dimension of the global critical incidence, extraction of its proper projected bad locus, effective degree bounds, and Katz's perverse-sheaf weak Lefschetz remain further work.

**Acceptance:** pinned Lean 4.35 kernel with axiom print, exact 144-case independent oracle, all MathCan compatibility CI. Keep draft until green.
