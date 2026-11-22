import Deligne04.AffineBertiniFiber
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# DEL-20: cotangent spanning for an actual polynomial embedded-product Jacobian

The previous DEL-19 parameter-surjectivity theorem required the
coordinate differentials to span the tangent cotangent space.
For a polynomial presentation of U^k, the actual Jacobian defines
the tangent subspace in the ambient coordinate vector space.

The coordinates on the ambient finite product restrict to linear
functionals on this subspace. By surjectivity of dual restriction
for vector spaces, *every* cotangent functional is a linear
combination of these restricted coordinate functionals. This
removes DEL-19's separate cotangent-spanning assumption for
the algebraically presented tangent space.

We use the true MvPolynomial.pderiv on the lifted product equations
from DEL-16. The geometric identification of the Jacobian-kernel
tangent space with the Zariski tangent space of an actual scheme
requires the presentation ideal and the usual tangent functor.
The dimension theorem for the critical incidence, geometric
proper-closure argument and Katz weak Lefschetz remain separate.
-/

open scoped BigOperators

namespace Deligne20

/-- Actual Jacobian-kernel tangent space for the polynomial
presentation of U^k. All entries use Mathlib's true pderiv. -/
noncomputable def jacobianTangent
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K) :
    Subspace K (Deligne16.Coord k s → K) := by
  classical
  refine {
    carrier := {v | ∀ t : Deligne16.EqCoord k r,
      (∑ i : Deligne16.Coord k s,
        MvPolynomial.eval u
          (MvPolynomial.pderiv i (Deligne16.copyEquation f t)) * v i) = 0}
    zero_mem' := ?_
    add_mem' := ?_
    smul_mem' := ?_ }
  · intro t
    simp
  · intro v w hv hw t
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hv t, hw t, zero_add]
  · intro a v hv t
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i : Deligne16.Coord k s,
        MvPolynomial.eval u
          (MvPolynomial.pderiv i (Deligne16.copyEquation f t)) * (a * v i)) =
          a * (∑ i : Deligne16.Coord k s,
            MvPolynomial.eval u
              (MvPolynomial.pderiv i (Deligne16.copyEquation f t)) * v i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = 0 := by rw [hv t, mul_zero]

/-- The subspace's membership predicate is precisely DEL-16's
real, polynomial-gradient tangent condition. -/
theorem mem_jacobianTangent_iff
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u v : Deligne16.Coord k s → K) :
    v ∈ jacobianTangent f u ↔ Deligne16.isProductTangent f u v := by
  rfl

/-- The coordinate-functional map from ambient coefficient vectors
to the dual of an arbitrary subspace W. This is the algebraic
cotangent restriction needed in the Bertini parameter map. -/
noncomputable def coordinateCotangent
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (W : Subspace K (σ → K)) (a : σ → K) : Module.Dual K W :=
  W.dualRestrict ((LinearMap.piRing K K σ K).symm a)

/-- The actual coordinate covectors span the entire cotangent of
every subspace of a finite ambient coordinate vector space.
Uses Mathlib's dual-extension theorem, without rank assumptions. -/
theorem coordinateCotangent_surjective
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (W : Subspace K (σ → K)) :
    Function.Surjective (coordinateCotangent W) := by
  classical
  intro phi
  obtain ⟨F, hF⟩ := W.dualRestrict_surjective phi
  refine ⟨(LinearMap.piRing K K σ K) F, ?_⟩
  simpa only [coordinateCotangent, LinearEquiv.symm_apply_apply] using hF

/-- An explicit finite sum formula for the cotangent spanning result,
as the restriction of an ambient linear functional to the actual
Jacobian-kernel tangent space. -/
theorem cotangent_eq_coordinate_sum
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (W : Subspace K (σ → K))
    (phi : Module.Dual K W) :
    ∃ a : σ → K, ∀ v : W,
      phi v = ∑ i : σ, a i * v.1 i := by
  classical
  obtain ⟨a, ha⟩ := coordinateCotangent_surjective W phi
  refine ⟨a, ?_⟩
  intro v
  have hval := congrArg (fun z : Module.Dual K W => z v) ha
  calc
    phi v = coordinateCotangent W a v := hval.symm
    _ = ((LinearMap.piRing K K σ K).symm a) (v : σ → K) := by
      simp only [coordinateCotangent, Submodule.dualRestrict_apply]
    _ = ∑ i : σ, (v.1 i) * a i := by
      simp only [LinearMap.piRing_symm_apply, smul_eq_mul]
    _ = ∑ i : σ, a i * v.1 i := by
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The previous result specializes to the actual pderiv-defined
tangent space of the embedded product from DEL-16. -/
theorem polynomial_product_cotangent_span
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (phi : Module.Dual K (jacobianTangent f u)) :
    ∃ a : Deligne16.Coord k s → K,
      ∀ v : jacobianTangent f u,
        phi v =
          ∑ i : Deligne16.Coord k s, a i * (v.1 i) := by
  exact cotangent_eq_coordinate_sum (jacobianTangent f u) phi

/-- The affine Bertini parameter map is surjective for the genuine
Jacobian-kernel cotangent: the freely variable constant c handles
the section value after the coordinate coefficients have set
the prescribed tangent differential. -/
theorem exists_parameter_for_jacobian_cotangent_and_value
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u z : Deligne16.Coord k s → K)
    (target : Module.Dual K (jacobianTangent f u))
    (level : K) :
    ∃ a : Deligne16.Coord k s → K, ∃ c : K,
      coordinateCotangent (jacobianTangent f u) a = target ∧
      Deligne19.parameterValue z a c = level := by
  obtain ⟨a, ha⟩ :=
    coordinateCotangent_surjective (jacobianTangent f u) target
  refine ⟨a, level - ∑ i : Deligne16.Coord k s, a i * z i, ha, ?_⟩
  dsimp [Deligne19.parameterValue]
  ring

/-- The fixed path-phase B can have any tangent differential dB:
choose affine hyperplane coefficients and constant so that both
the section and its differential vanish at the chosen point. -/
theorem exists_fixed_phase_critical_on_jacobian_tangent
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u z : Deligne16.Coord k s → K)
    (B : K) (dB : Module.Dual K (jacobianTangent f u)) :
    ∃ a : Deligne16.Coord k s → K, ∃ c : K,
      coordinateCotangent (jacobianTangent f u) a = -dB ∧
      B + Deligne19.parameterValue z a c = 0 := by
  obtain ⟨a, c, ha, hv⟩ :=
    exists_parameter_for_jacobian_cotangent_and_value f u z (-dB) (-B)
  refine ⟨a, c, ha, ?_⟩
  rw [hv]
  ring

#print axioms mem_jacobianTangent_iff
#print axioms coordinateCotangent_surjective
#print axioms cotangent_eq_coordinate_sum
#print axioms polynomial_product_cotangent_span
#print axioms exists_parameter_for_jacobian_cotangent_and_value
#print axioms exists_fixed_phase_critical_on_jacobian_tangent

end Deligne20
