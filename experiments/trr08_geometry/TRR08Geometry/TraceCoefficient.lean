module

public import TRR08Geometry.LocalCoefficient
public import TRR08Geometry.FiniteSlopeAverage

/-!
# The second local coefficient from a finite coordinate trace

The coordinate trace is a sum over an actual finite subgroup. Translation and
inversion of that subgroup derive its relation to the reciprocal sums. The
proof uses the Weierstrass addition formula and has no hypothesis asserting a
trace identity or a global residue identity.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve
open scoped BigOperators

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

noncomputable def subgroupXTrace (H : AddSubgroup W.Point) [Fintype H] : K :=
  ∑ Q : H, affineX (Q : W.Point)

noncomputable def reciprocalTrace (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : K :=
  ∑ Q ∈ coefficientOthers H P, 1 / (affineX (P : W.Point) - affineX (Q : W.Point))

noncomputable def reciprocalSquareTrace (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : K :=
  ∑ Q ∈ coefficientOthers H P, 1 / (affineX (P : W.Point) - affineX (Q : W.Point)) ^ 2

noncomputable def localSecondCoefficient (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : K :=
  ((3 * affineX (P : W.Point)^2 + W.a₄) / (2 * affineY (P : W.Point)))^2 -
    2 * affineX (P : W.Point) +
    (affineY (P : W.Point)^2 / 2) * (reciprocalTrace H P)^2 +
    affineY (P : W.Point)^2 * reciprocalSquareTrace H P

/-- Splitting the three distinguished points from an actual subgroup sum. -/
theorem coefficient_sum_split (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hdouble : P + P ≠ 0) (f : H → K) :
    (∑ Q : H, f Q) = f 0 + f P + f (-P) +
      ∑ Q ∈ coefficientOthers H P, f Q := by
  classical
  have hnP : P ≠ -P := fun h => hdouble (eq_neg_iff_add_eq_zero.mp h)
  have hn0 : (-P : H) ≠ 0 := neg_ne_zero.mpr hP
  have he (Q : H) : f Q =
      (if Q = 0 then f 0 else 0) + (if Q = P then f P else 0) +
      (if Q = -P then f (-P) else 0) +
      (if Q ∈ coefficientOthers H P then f Q else 0) := by
    by_cases hQ0 : Q = 0
    · subst Q
      simp [Ne.symm hP, Ne.symm hn0]
    by_cases hQP : Q = P
    · subst Q
      simp [hP, hnP]
    by_cases hQnP : Q = -P
    · subst Q
      simp [hn0, Ne.symm hnP]
    · simp [hQ0, hQP, hQnP]
  calc
    (∑ Q : H, f Q) = ∑ Q : H,
        ((if Q = 0 then f 0 else 0) + (if Q = P then f P else 0) +
        (if Q = -P then f (-P) else 0) +
        (if Q ∈ coefficientOthers H P then f Q else 0)) :=
      Finset.sum_congr rfl (fun Q _ => he Q)
    _ = f 0 + f P + f (-P) + ∑ Q ∈ coefficientOthers H P, f Q := by
      simp only [Finset.sum_add_distrib]
      simp [coefficientOthers, Finset.sum_filter]

/-- The cardinal coefficient is obtained without dividing by the subgroup order. -/
theorem coefficientOthers_card_cast (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hdouble : P + P ≠ 0) :
    ((coefficientOthers H P).card : K) = (Fintype.card H : K) - 3 := by
  have hs := coefficient_sum_split H P hP hdouble (fun _ => (1 : K))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  linear_combination -hs

omit [DecidableEq K] in
private theorem paired_x_algebra (x y z w A B : K)
    (hx : x - z ≠ 0) (hp : y^2 = x^3 + A*x + B)
    (hq : w^2 = z^3 + A*z + B) :
    (((y-w)/(x-z))^2-x-z) + (((y+w)/(x-z))^2-x-z) =
      2*x - 2*(3*x^2+A)/(x-z) + 4*y^2/(x-z)^2 := by
  field_simp [hx]
  linear_combination 2 * hq - 2 * hp

/-- The paired coordinate formula follows from the actual point addition law. -/
theorem paired_add_x {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : affineX P ≠ affineX Q) :
    affineX (P + Q) + affineX (P - Q) =
      2 * affineX P - 2 * (3 * affineX P^2 + W.a₄) / (affineX P - affineX Q) +
      4 * affineY P^2 / (affineX P - affineX Q)^2 := by
  have hadd : P + Q ≠ 0 := by
    intro h
    have he : P = -Q := eq_neg_iff_add_eq_zero.mpr h
    exact hx (by rw [he, affineX_neg])
  have hsub : P + -Q ≠ 0 := by
    intro h
    have he : P = Q := by simpa using (eq_neg_iff_add_eq_zero.mpr h)
    exact hx (congrArg affineX he)
  rw [sub_eq_add_neg, normalizedSlope_add_x hP hQ hadd,
    normalizedSlope_add_x hP (neg_ne_zero.mpr hQ) hsub,
    normalizedSlope_of_x_ne hP hQ hx,
    normalizedSlope_of_x_ne hP (neg_ne_zero.mpr hQ) (by simpa using hx)]
  simp only [affineX_neg, affineY_neg, sub_neg_eq_add]
  exact paired_x_algebra _ _ _ _ _ _ (sub_ne_zero.mpr hx)
    (short_curve_equation hP) (short_curve_equation hQ)

omit [W.IsShortNF] in
/-- Translation of all subgroup points gives the same coordinate trace. -/
theorem subgroupXTrace_translate (H : AddSubgroup W.Point) [Fintype H] (P : H) :
    (∑ Q : H, affineX ((P + Q : H) : W.Point)) = subgroupXTrace H := by
  exact Fintype.sum_equiv (Equiv.addLeft P)
    (fun Q => affineX ((P + Q : H) : W.Point))
    (fun Q => affineX (Q : W.Point)) (fun _ => rfl)

/-- Removing the three distinguished points from the translated trace. -/
theorem subgroupXTrace_translate_others (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hdouble : P + P ≠ 0) :
    (∑ Q ∈ coefficientOthers H P, affineX ((P + Q : H) : W.Point)) =
      subgroupXTrace H + affineX (P : W.Point) -
        ((3 * affineX (P : W.Point)^2 + W.a₄) / (2 * affineY (P : W.Point)))^2 := by
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hd : (P : W.Point) + (P : W.Point) ≠ 0 := fun h => hdouble (Subtype.ext h)
  have hs := coefficient_sum_split H P hP hdouble
    (fun Q => affineX ((P + Q : H) : W.Point))
  rw [subgroupXTrace_translate] at hs
  have hx0 : affineX (0 : W.Point) = 0 := rfl
  simp only [add_zero, add_neg_cancel, AddSubgroup.coe_zero, AddSubgroup.coe_add,
    hx0, add_zero] at hs
  rw [short_doubling_x hp hd] at hs
  linear_combination -hs

/-- A finite trace formula derived by pairing actual subgroup points. -/
theorem subgroupXTrace_eq_reciprocal (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hdouble : P + P ≠ 0) (h₂ : (2 : K) ≠ 0) :
    subgroupXTrace H =
      ((3 * affineX (P : W.Point)^2 + W.a₄) / (2 * affineY (P : W.Point)))^2 +
      ((Fintype.card H : K) - 4) * affineX (P : W.Point) -
      (3 * affineX (P : W.Point)^2 + W.a₄) * reciprocalTrace H P +
      2 * affineY (P : W.Point)^2 * reciprocalSquareTrace H P := by
  classical
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  let s := coefficientOthers H P
  let f : H → K := fun Q => affineX ((P + Q : H) : W.Point)
  have hi : (∑ Q ∈ s, f (-Q)) = ∑ Q ∈ s, f Q := coefficientOthers_neg_sum H P f
  have hpairs : 2 * (∑ Q ∈ s, f Q) =
      2 * (s.card : K) * affineX (P : W.Point) -
      2 * (3 * affineX (P : W.Point)^2 + W.a₄) * reciprocalTrace H P +
      4 * affineY (P : W.Point)^2 * reciprocalSquareTrace H P := by
    calc
      2 * (∑ Q ∈ s, f Q) = ∑ Q ∈ s, (f Q + f (-Q)) := by
        rw [Finset.sum_add_distrib, hi]
        ring
      _ = ∑ Q ∈ s,
          (2 * affineX (P : W.Point) -
          2 * (3 * affineX (P : W.Point)^2 + W.a₄) *
            (1 / (affineX (P : W.Point) - affineX (Q : W.Point))) +
          4 * affineY (P : W.Point)^2 *
            (1 / (affineX (P : W.Point) - affineX (Q : W.Point))^2)) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        have hq : (Q : W.Point) ≠ 0 :=
          fun h => (mem_coefficientOthers.mp hQ).1 (Subtype.ext h)
        have hpair := paired_add_x hp hq (coefficientOthers_x_ne hP hQ)
        simpa [f, sub_eq_add_neg, div_eq_mul_inv] using hpair
      _ = 2 * (s.card : K) * affineX (P : W.Point) -
          2 * (3 * affineX (P : W.Point)^2 + W.a₄) * reciprocalTrace H P +
          4 * affineY (P : W.Point)^2 * reciprocalSquareTrace H P := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
        change _ = _ - _ * (∑ Q ∈ s, _) + _ * (∑ Q ∈ s, _)
        ring
  have ht := subgroupXTrace_translate_others H P hP hdouble
  change (∑ Q ∈ s, f Q) = _ at ht
  rw [ht, coefficientOthers_card_cast H P hP hdouble] at hpairs
  apply mul_left_cancel₀ h₂
  linear_combination hpairs

/-- The second coefficient and the slope coefficient have a common finite trace. -/
theorem localSecondCoefficient_relation (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hdouble : P + P ≠ 0) (h₂ : (2 : K) ≠ 0) :
    2 * localSecondCoefficient H P - (slopeCoefficient H P)^2 +
      (Fintype.card H : K) * affineX (P : W.Point) = subgroupXTrace H := by
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hd : (P : W.Point) + (P : W.Point) ≠ 0 := fun h => hdouble (Subtype.ext h)
  have hy : affineY (P : W.Point) ≠ 0 := short_y_ne_zero hp hd
  rw [subgroupXTrace_eq_reciprocal H P hP hdouble h₂,
    slopeCoefficient_eq_unpaired H P hP hdouble h₂]
  change 2 * localSecondCoefficient H P -
    (-((3 * affineX (P : W.Point)^2 + W.a₄) / (2 * affineY (P : W.Point))) -
      affineY (P : W.Point) * reciprocalTrace H P)^2 + _ = _
  unfold localSecondCoefficient
  field_simp
  ring

end TRR08Geometry

#print axioms TRR08Geometry.coefficient_sum_split
#print axioms TRR08Geometry.coefficientOthers_card_cast
#print axioms TRR08Geometry.paired_add_x
#print axioms TRR08Geometry.subgroupXTrace_translate
#print axioms TRR08Geometry.subgroupXTrace_translate_others
#print axioms TRR08Geometry.subgroupXTrace_eq_reciprocal
#print axioms TRR08Geometry.localSecondCoefficient_relation
