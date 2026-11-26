module

public import TRR08Geometry.NormalizedSlope
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The local coefficient as a finite sum of actual slopes

The odd subgroup hypothesis makes every nonidentity x-coordinate occur twice.
Pairing a point with its negative identifies the explicit reciprocal-root
formula with the negative sum of normalized chord and tangent slopes.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve
open scoped BigOperators

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

theorem normalizedSlope_pair {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : affineX P ≠ affineX Q) :
    normalizedSlope P Q + normalizedSlope P (-Q) =
      2 * affineY P / (affineX P - affineX Q) := by
  rw [normalizedSlope_of_x_ne hP hQ hx,
    normalizedSlope_of_x_ne hP (neg_ne_zero.mpr hQ) (by simpa using hx)]
  simp only [affineX_neg, affineY_neg]
  rw [← add_div]
  congr 1
  ring

noncomputable def coefficientOthers (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : Finset H := by
  classical
  exact Finset.univ.filter (fun Q => Q ≠ 0 ∧ Q ≠ P ∧ Q ≠ -P)

noncomputable def subgroupXRoots (H : AddSubgroup W.Point) [Fintype H] : Finset K := by
  classical
  exact (Finset.univ.erase (0 : H)).image (fun Q : H => affineX (Q : W.Point))

noncomputable def slopeCoefficient (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : K := -∑ Q : H, normalizedSlope (P : W.Point) (Q : W.Point)

noncomputable def localCoefficient (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : K :=
  -((3 * affineX (P : W.Point)^2 + W.a₄) / (2 * affineY (P : W.Point))) -
    2 * affineY (P : W.Point) *
      ∑ v ∈ (subgroupXRoots H).erase (affineX (P : W.Point)),
        1 / (affineX (P : W.Point) - v)

@[simp] theorem mem_coefficientOthers {H : AddSubgroup W.Point} [Fintype H]
    {P Q : H} : Q ∈ coefficientOthers H P ↔ Q ≠ 0 ∧ Q ≠ P ∧ Q ≠ -P := by
  classical
  simp [coefficientOthers]

theorem neg_mem_coefficientOthers {H : AddSubgroup W.Point} [Fintype H]
    {P Q : H} (hQ : Q ∈ coefficientOthers H P) : -Q ∈ coefficientOthers H P := by
  rcases mem_coefficientOthers.mp hQ with ⟨h0, hP, hnP⟩
  apply mem_coefficientOthers.mpr
  constructor
  · exact neg_ne_zero.mpr h0
  constructor
  · intro h
    exact hnP (by simpa using congrArg Neg.neg h)
  · intro h
    exact hP (neg_injective h)

theorem coefficientOthers_x_ne {H : AddSubgroup W.Point} [Fintype H]
    {P Q : H} (hP : P ≠ 0) (hQ : Q ∈ coefficientOthers H P) :
    affineX (P : W.Point) ≠ affineX (Q : W.Point) := by
  rcases mem_coefficientOthers.mp hQ with ⟨hQ0, hQP, hQnP⟩
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hq : (Q : W.Point) ≠ 0 := fun h => hQ0 (Subtype.ext h)
  intro hx
  rcases (affineX_eq_iff hp hq).mp hx with h | h
  · exact hQP (Subtype.ext h.symm)
  · have he : P = -Q := Subtype.ext h
    exact hQnP (by rw [he]; simp)

theorem coefficientOthers_neg_sum (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (f : H → K) :
    (∑ Q ∈ coefficientOthers H P, f (-Q)) =
      ∑ Q ∈ coefficientOthers H P, f Q := by
  classical
  apply Finset.sum_bij (fun Q _ => -Q)
  · intro Q hQ
    exact neg_mem_coefficientOthers hQ
  · intro Q hQ R hR h
    exact neg_injective h
  · intro Q hQ
    exact ⟨-Q, neg_mem_coefficientOthers hQ, neg_neg Q⟩
  · intro Q hQ
    rfl

theorem slope_sum_split (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) :
    (∑ Q : H, normalizedSlope (P : W.Point) (Q : W.Point)) =
      normalizedSlope (P : W.Point) (P : W.Point) +
        ∑ Q ∈ coefficientOthers H P, normalizedSlope (P : W.Point) (Q : W.Point) := by
  classical
  let f : H → K := fun Q => normalizedSlope (P : W.Point) (Q : W.Point)
  have he (Q : H) : f Q = (if Q = P then f P else 0) +
      (if Q ∈ coefficientOthers H P then f Q else 0) := by
    by_cases hQP : Q = P
    · subst Q
      simp [hP]
    by_cases hQ0 : Q = 0
    · subst Q
      simp [f, hQP]
    by_cases hQnP : Q = -P
    · subst Q
      simp [f, hQP]
    · simp [hQP, mem_coefficientOthers, hQ0, hQnP]
  change (∑ Q : H, f Q) = f P + ∑ Q ∈ coefficientOthers H P, f Q
  calc
    (∑ Q : H, f Q) = ∑ Q : H,
        ((if Q = P then f P else 0) + (if Q ∈ coefficientOthers H P then f Q else 0)) :=
      Finset.sum_congr rfl (fun Q _ => he Q)
    _ = f P + ∑ Q ∈ coefficientOthers H P, f Q := by
      rw [Finset.sum_add_distrib]
      simp [coefficientOthers, Finset.sum_filter]

theorem slopeCoefficient_eq_unpaired (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hdouble : P + P ≠ 0) (h₂ : (2 : K) ≠ 0) :
    slopeCoefficient H P =
      -((3 * affineX (P : W.Point)^2 + W.a₄) / (2 * affineY (P : W.Point))) -
        affineY (P : W.Point) *
          ∑ Q ∈ coefficientOthers H P, 1 / (affineX (P : W.Point) - affineX (Q : W.Point)) := by
  classical
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hd : (P : W.Point) + (P : W.Point) ≠ 0 := fun h => hdouble (Subtype.ext h)
  let s := coefficientOthers H P
  let f : H → K := fun Q => normalizedSlope (P : W.Point) (Q : W.Point)
  let g : H → K := fun Q => 1 / (affineX (P : W.Point) - affineX (Q : W.Point))
  have hi : (∑ Q ∈ s, f (-Q)) = ∑ Q ∈ s, f Q := coefficientOthers_neg_sum H P f
  have he : 2 * (∑ Q ∈ s, f Q) =
      2 * (affineY (P : W.Point) * ∑ Q ∈ s, g Q) := by
    calc
      2 * (∑ Q ∈ s, f Q) = (∑ Q ∈ s, f Q) + ∑ Q ∈ s, f (-Q) := by rw [hi]; ring
      _ = ∑ Q ∈ s, (f Q + f (-Q)) := (Finset.sum_add_distrib).symm
      _ = ∑ Q ∈ s, (2 * affineY (P : W.Point) * g Q) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        have hq : (Q : W.Point) ≠ 0 := fun h => (mem_coefficientOthers.mp hQ).1 (Subtype.ext h)
        have paired := normalizedSlope_pair hp hq (coefficientOthers_x_ne hP hQ)
        simpa [f, g, div_eq_mul_inv] using paired
      _ = 2 * (affineY (P : W.Point) * ∑ Q ∈ s, g Q) := by
        rw [← Finset.mul_sum]
        ring
  have hc : (∑ Q ∈ s, f Q) = affineY (P : W.Point) * ∑ Q ∈ s, g Q :=
    mul_left_cancel₀ h₂ he
  unfold slopeCoefficient
  rw [slope_sum_split H P hP, normalizedSlope_self hp hd]
  change -(_ + ∑ Q ∈ s, f Q) = _
  rw [hc]
  ring

theorem coefficientOthers_image (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) :
    (coefficientOthers H P).image (fun Q : H => affineX (Q : W.Point)) =
      (subgroupXRoots H).erase (affineX (P : W.Point)) := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨Q, hQ, rfl⟩
    apply Finset.mem_erase.mpr
    refine ⟨Ne.symm (coefficientOthers_x_ne hP hQ), ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨Q, by simpa using (mem_coefficientOthers.mp hQ).1, rfl⟩
  · intro hv
    rcases Finset.mem_erase.mp hv with ⟨hne, hv⟩
    rcases Finset.mem_image.mp hv with ⟨Q, hQ, hx⟩
    apply Finset.mem_image.mpr
    refine ⟨Q, mem_coefficientOthers.mpr ⟨?_, ?_, ?_⟩, hx⟩
    · simpa using hQ
    · intro h
      subst Q
      exact hne hx.symm
    · intro h
      subst Q
      exact hne (by simpa using hx.symm)

theorem coefficientOthers_fiber (H : AddSubgroup W.Point) [Fintype H]
    (P Q : H) (hQ : Q ∈ coefficientOthers H P) :
    (coefficientOthers H P).filter (fun R : H => affineX (R : W.Point) = affineX (Q : W.Point)) =
      {Q, -Q} := by
  classical
  ext R
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hR, hx⟩
    have hr : (R : W.Point) ≠ 0 := fun h => (mem_coefficientOthers.mp hR).1 (Subtype.ext h)
    have hq : (Q : W.Point) ≠ 0 := fun h => (mem_coefficientOthers.mp hQ).1 (Subtype.ext h)
    rcases (affineX_eq_iff hr hq).mp hx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact ⟨hQ, rfl⟩
    · exact ⟨neg_mem_coefficientOthers hQ, by simp⟩

theorem coefficientOthers_sum_by_roots (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (f : K → K) :
    (∑ Q ∈ coefficientOthers H P, f (affineX (Q : W.Point))) =
      2 * ∑ v ∈ (subgroupXRoots H).erase (affineX (P : W.Point)), f v := by
  classical
  rw [← coefficientOthers_image H P hP]
  let s := coefficientOthers H P
  let x : H → K := fun Q => affineX (Q : W.Point)
  have hf := Finset.sum_fiberwise_of_maps_to' (s := s) (t := s.image x) (g := x)
    (fun Q hQ => Finset.mem_image_of_mem x hQ) f
  calc
    (∑ Q ∈ s, f (x Q)) = ∑ v ∈ s.image x, ∑ Q ∈ s with x Q = v, f v := hf.symm
    _ = ∑ v ∈ s.image x, 2 * f v := by
      apply Finset.sum_congr rfl
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨Q, hQ, rfl⟩
      have he : s.filter (fun R => x R = x Q) = {Q, -Q} := coefficientOthers_fiber H P Q hQ
      rw [he]
      simp [hno2 Q (mem_coefficientOthers.mp hQ).1, two_mul]
    _ = 2 * ∑ v ∈ s.image x, f v := (Finset.mul_sum _ _ _).symm

/-- The explicit reciprocal-root coefficient equals the negative finite slope sum. -/
theorem localCoefficient_eq_slopeCoefficient (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) :
    localCoefficient H P = slopeCoefficient H P := by
  have hd : P + P ≠ 0 := by
    intro h
    exact hno2 P hP (eq_neg_iff_add_eq_zero.mpr h)
  rw [slopeCoefficient_eq_unpaired H P hP hd h₂,
    coefficientOthers_sum_by_roots H P hP hno2
      (fun v => 1 / (affineX (P : W.Point) - v))]
  unfold localCoefficient
  ring

#print axioms normalizedSlope_pair
#print axioms slopeCoefficient_eq_unpaired
#print axioms coefficientOthers_image
#print axioms coefficientOthers_fiber
#print axioms coefficientOthers_sum_by_roots
#print axioms localCoefficient_eq_slopeCoefficient

end TRR08Geometry
