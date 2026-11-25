module

public import TRR08Geometry.ExplicitObstruction

/-!
# The reciprocal-root coefficient on an odd cyclic subgroup

Odd marked order excludes nonidentity self-negative elements. This supplies
the hypothesis for the finite pairing theorem directly from the group order.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

omit [W.IsShortNF] in
/-- Odd order of the marked point excludes nonzero two-torsion throughout
its actual cyclic subgroup. -/
theorem cyclic_ne_neg_of_odd_order (T : W.Point) (hodd : Odd (addOrderOf T))
    (Q : AddSubgroup.zmultiples T) (hQ : Q ≠ 0) : Q ≠ -Q := by
  intro hself
  have hd : (Q : W.Point) + (Q : W.Point) = 0 := by
    have he : (Q : W.Point) = -(Q : W.Point) := congrArg Subtype.val hself
    exact eq_neg_iff_add_eq_zero.mp he
  have hn : (addOrderOf T) • (Q : W.Point) = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_of_mem_zmultiples Q.property)
  rcases hodd with ⟨k, hk⟩
  have hmul : (2 * k) • (Q : W.Point) = 0 := by
    rw [mul_nsmul, two_nsmul, hd, nsmul_zero]
  rw [hk, add_nsmul, one_nsmul, hmul, zero_add] at hn
  exact hQ (Subtype.ext hn)

/-- The actual positive multiple as an element of its cyclic subgroup. -/
def cyclicMultiple (T : W.Point) (k : ℕ) : AddSubgroup.zmultiples T :=
  ⟨k • T, ⟨(k : ℤ), by simp⟩⟩

/-- This form uses the canonical finite enumeration chosen for the cyclic
coefficient, so its row sum is definitionally the same finite sum. -/
theorem localCoefficient_cyclic_eq (T : W.Point) (hfin : IsOfFinAddOrder T)
    (hodd : Odd (addOrderOf T)) (h₂ : (2 : K) ≠ 0)
    (k : ℕ) (hk : k • T ≠ 0) :
    letI := FiniteSlopeAverage.cyclicFintype T hfin;
    localCoefficient (AddSubgroup.zmultiples T) (cyclicMultiple T k) =
      cyclicSlopeCoefficient T hfin k := by
  let := FiniteSlopeAverage.cyclicFintype T hfin
  have hP : cyclicMultiple T k ≠ 0 := fun h => hk (congrArg Subtype.val h)
  have hs := localCoefficient_eq_slopeCoefficient (AddSubgroup.zmultiples T)
    (cyclicMultiple T k) hP (cyclic_ne_neg_of_odd_order T hodd) h₂
  simpa only [slopeCoefficient, cyclicMultiple, cyclicSlopeCoefficient,
    FiniteSlopeAverage.cyclicCoefficient] using hs

end TRR08Geometry

#print axioms TRR08Geometry.cyclic_ne_neg_of_odd_order
#print axioms TRR08Geometry.localCoefficient_cyclic_eq
