import Deligne04.JacobianTangentCotangent
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic

/-!
# DEL-21A: scheme-sensitive tangent vectors through dual numbers

For a genuine polynomial presentation P=K[z_i] and ideal I=(g_t),
a point u of Spec(P/I) has a first-order tangent vector v exactly
when the map sending each z_i to u_i+epsilon*v_i extends from P
to P/I over K[epsilon]/(epsilon²).

We construct a ring homomorphism into Mathlib's actual DualNumber K
using the formal partial derivatives of multivariate polynomials.
Its value on P is (eval_u P, sum_i eval_u(pderiv_i P)*v_i).

Its kernel contains I precisely when the first-order values on
every *ideal generator* are zero. This is sensitive to the scheme
ideal, including nilpotents; taking only the radical can change
the first-order tangent functor.

In the actual DEL-16 embedded U^k presentation, first-order lifts
of the quotient-ring point correspond exactly to DEL-20's
Jacobian-kernel tangent vectors. The Kähler-fiber/derivation
equivalence and subsequent global geometric incidence theorem
remain separate DEL-21 proof obligations.
-/

open scoped BigOperators
open Finset

namespace Deligne21

/-- The directional derivative evaluated at a point, computed
from genuine Mathlib polynomial partial derivatives. -/
noncomputable def tangentDerivative
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) (P : MvPolynomial σ K) : K :=
  ∑ i : σ,
    MvPolynomial.eval u (MvPolynomial.pderiv i P) * v i

theorem tangentDerivative_zero
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) :
    tangentDerivative u v (0 : MvPolynomial σ K) = 0 := by
  simp [tangentDerivative]

theorem tangentDerivative_one
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) :
    tangentDerivative u v (1 : MvPolynomial σ K) = 0 := by
  simp [tangentDerivative]

theorem tangentDerivative_add
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) (P Q : MvPolynomial σ K) :
    tangentDerivative u v (P + Q) =
      tangentDerivative u v P + tangentDerivative u v Q := by
  simp only [tangentDerivative, map_add, add_mul, Finset.sum_add_distrib]

theorem tangentDerivative_mul
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) (P Q : MvPolynomial σ K) :
    tangentDerivative u v (P * Q) =
      MvPolynomial.eval u P * tangentDerivative u v Q +
      tangentDerivative u v P * MvPolynomial.eval u Q := by
  classical
  calc
    tangentDerivative u v (P * Q) =
        ∑ i : σ,
          (MvPolynomial.eval u P *
              (MvPolynomial.eval u (MvPolynomial.pderiv i Q) * v i) +
            (MvPolynomial.eval u (MvPolynomial.pderiv i P) * v i) *
              MvPolynomial.eval u Q) := by
        simp only [tangentDerivative]
        apply Finset.sum_congr rfl
        intro i _
        rw [MvPolynomial.pderiv_mul]
        simp only [map_add, map_mul]
        ring
    _ = MvPolynomial.eval u P * tangentDerivative u v Q +
          tangentDerivative u v P * MvPolynomial.eval u Q := by
        simp only [tangentDerivative, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.sum_mul]

/-- The actual dual-number evaluation homomorphism. The first
component is polynomial evaluation at u, and the nilpotent
component is the directional derivative along v. -/
noncomputable def firstOrderEvaluation
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) : MvPolynomial σ K →+* DualNumber K where
  toFun := fun P => (MvPolynomial.eval u P, tangentDerivative u v P)
  map_zero' := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [tangentDerivative_zero]
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [tangentDerivative_one]
  map_add' := by
    intro P Q
    change (MvPolynomial.eval u (P + Q), tangentDerivative u v (P + Q)) =
      (MvPolynomial.eval u P + MvPolynomial.eval u Q,
        tangentDerivative u v P + tangentDerivative u v Q)
    simp only [map_add, tangentDerivative_add]
  map_mul' := by
    intro P Q
    change (MvPolynomial.eval u (P * Q), tangentDerivative u v (P * Q)) =
      (MvPolynomial.eval u P * MvPolynomial.eval u Q,
        MvPolynomial.eval u P * tangentDerivative u v Q +
          tangentDerivative u v P * MvPolynomial.eval u Q)
    simp only [map_mul, tangentDerivative_mul]

/-- A polynomial evaluates to zero in the actual dual-number
algebra exactly when both its value and its differential vanish. -/
theorem firstOrderEvaluation_eq_zero_iff
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) (P : MvPolynomial σ K) :
    firstOrderEvaluation u v P = 0 ↔
      MvPolynomial.eval u P = 0 ∧ tangentDerivative u v P = 0 := by
  change (MvPolynomial.eval u P, tangentDerivative u v P) =
    ((0 : K), (0 : K)) ↔ _
  exact Prod.mk.injEq

/-- For a genuine defining ideal, a dual-number homomorphism
annihilates the entire ideal iff it annihilates each generator.
This is an equality of ring-homomorphism kernels, not an
assertion only about rational-point zero sets. -/
theorem firstOrder_ideal_iff_generators
    {K : Type*} [Field K] {σ τ : Type*} [Fintype σ]
    (g : τ → MvPolynomial σ K) (u v : σ → K) :
    (∀ P : MvPolynomial σ K,
      P ∈ Ideal.span (Set.range g) →
        firstOrderEvaluation u v P = 0) ↔
      (∀ t : τ, firstOrderEvaluation u v (g t) = 0) := by
  constructor
  · intro h t
    exact h (g t) (Ideal.subset_span (Set.mem_range_self t))
  · intro h P hP
    have hle :
        Ideal.span (Set.range g) ≤
          RingHom.ker (firstOrderEvaluation u v) := by
      apply Ideal.span_le.mpr
      rintro Q ⟨t, rfl⟩
      change firstOrderEvaluation u v (g t) = 0
      exact h t
    exact hle hP

/-- A genuine quotient-ring morphism into dual numbers exists
precisely when all defining-ideal polynomials vanish to first
order. The lift is a ring homomorphism on the actual quotient
P/I and thus keeps nilpotent scheme structure. -/
theorem firstOrder_factors_through_quotient_iff
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (u v : σ → K) :
    (∃ F : (MvPolynomial σ K ⧸ I) →+* DualNumber K,
      F.comp (Ideal.Quotient.mk I) = firstOrderEvaluation u v) ↔
    (∀ P : MvPolynomial σ K,
      P ∈ I → firstOrderEvaluation u v P = 0) := by
  constructor
  · rintro ⟨F, hF⟩ P hP
    have hzero : (Ideal.Quotient.mk I) P = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hP
    have heq := congrArg (fun H : MvPolynomial σ K →+* DualNumber K => H P) hF
    simp only [RingHom.comp_apply, hzero, map_zero] at heq
    exact heq.symm
  · intro h
    have hle : I ≤ RingHom.ker (firstOrderEvaluation u v) := by
      intro P hP
      change firstOrderEvaluation u v P = 0
      exact h P hP
    refine ⟨Ideal.Quotient.lift I (firstOrderEvaluation u v) hle, ?_⟩
    rfl

/-- DEL-20's true MvPolynomial Jacobian-kernel tangent vectors
are precisely first-order deformations of the *actual* quotient
K[coordinates of U^k]/(lifted defining equations). The theorem
requires the base point to satisfy every ideal generator. -/
theorem product_jacobian_tangent_iff_firstOrder_lift
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u v : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u) :
    v ∈ Deligne20.jacobianTangent f u ↔
      ∃ F : (MvPolynomial (Deligne16.Coord k s) K ⧸
          Deligne16.productIdeal f) →+* DualNumber K,
        F.comp (Ideal.Quotient.mk (Deligne16.productIdeal f)) =
          firstOrderEvaluation u v := by
  rw [firstOrder_factors_through_quotient_iff]
  constructor
  · intro hv P hP
    have htan := (Deligne20.mem_jacobianTangent_iff f u v).mp hv
    have hgens : ∀ t : Deligne16.EqCoord k r,
        firstOrderEvaluation u v (Deligne16.copyEquation f t) = 0 := by
      intro t
      apply (firstOrderEvaluation_eq_zero_iff u v _).mpr
      exact ⟨hu t, htan t⟩
    exact (firstOrder_ideal_iff_generators
      (Deligne16.copyEquation f) u v).mpr hgens P hP
  · intro h
    apply (Deligne20.mem_jacobianTangent_iff f u v).mpr
    intro t
    have hmem : Deligne16.copyEquation f t ∈ Deligne16.productIdeal f :=
      Ideal.subset_span (Set.mem_range_self t)
    have hzero := h _ hmem
    exact ((firstOrderEvaluation_eq_zero_iff u v _).mp hzero).2

#print axioms tangentDerivative_mul
#print axioms firstOrderEvaluation_eq_zero_iff
#print axioms firstOrder_ideal_iff_generators
#print axioms firstOrder_factors_through_quotient_iff
#print axioms product_jacobian_tangent_iff_firstOrder_lift

end Deligne21
