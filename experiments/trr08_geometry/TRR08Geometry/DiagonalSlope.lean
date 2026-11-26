module

public import TRR08Geometry.NormalizedSlope

/-!
# The diagonal cocycle for actual normalized slopes

The secant and tangent identities apply to Mathlib's affine point group.
The case split includes identity points, inverse pairs and torsion
coincidences, so the theorem requires no generic-position hypothesis.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K}

theorem normalizedSlope_of_add_eq_zero {P Q : W.Point} (h : P + Q = 0) :
    normalizedSlope P Q = 0 := by
  have he : P = -Q := (eq_neg_iff_add_eq_zero).mpr h
  rw [he]
  exact normalizedSlope_neg_left Q

variable [W.IsShortNF]

/-- The normalized chord/tangent slope satisfies the diagonal cocycle on the
actual nonsingular point group, including all identity and inverse cases. -/
theorem normalizedSlope_diagonal (P R : W.Point) :
    normalizedSlope P P + normalizedSlope (P + P) R =
      normalizedSlope P R + normalizedSlope P (P + R) := by
  by_cases hP : P = 0
  · subst P
    simp
  by_cases hD : P + P = 0
  · have hm := normalizedSlope_of_add_eq_zero hD
    rw [hm, hD, normalizedSlope_zero_left, zero_add]
    by_cases hR : R = 0
    · subst R
      simp only [normalizedSlope_zero_right, add_zero, hm]
    by_cases hE : P + R = 0
    · rw [normalizedSlope_of_add_eq_zero hE, hE, normalizedSlope_zero_right, add_zero]
    have hneg : -P = P := ((eq_neg_iff_add_eq_zero).mpr hD).symm
    have hs := normalizedSlope_sum_neg hR hP (by simpa only [add_comm] using hE)
    rw [add_comm R P, hneg, normalizedSlope_comm (P + R) P,
      normalizedSlope_comm R P] at hs
    rw [hs, add_neg_cancel]
  by_cases hR : R = 0
  · subst R
    simp
  by_cases hRneg : R = -P
  · subst R
    rw [normalizedSlope_sum_neg hP hP hD]
    simp
  by_cases hRnegD : R = -(P + P)
  · subst R
    have hsum : P + -(P + P) = -P := by
      rw [neg_add, ← add_assoc, add_neg_cancel, zero_add]
    rw [normalizedSlope_neg_right, hsum, normalizedSlope_neg_right, add_zero, add_zero]
    exact normalizedSlope_rotate hP hP hD
  by_cases hRsame : R = P
  · subst R
    rw [normalizedSlope_comm (P + P) P]
  have hE : P + R ≠ 0 := by
    intro hz
    apply hRneg
    exact (eq_neg_iff_add_eq_zero).mpr (by simpa only [add_comm] using hz)
  have hF : (P + P) + R ≠ 0 := by
    intro hz
    apply hRnegD
    exact (eq_neg_iff_add_eq_zero).mpr (by simpa only [add_comm] using hz)
  by_cases hRdouble : R = P + P
  · subst R
    exact normalizedSlope_diagonal_double hP hD hE hF
  have hxD : affineX (P + P) ≠ affineX R := by
    intro he
    rcases (affineX_eq_iff hD hR).mp he with hs | hn
    · exact hRdouble hs.symm
    · apply hRnegD
      have hh := congrArg Neg.neg hn
      simpa only [neg_neg] using hh.symm
  have hxE : affineX P ≠ affineX (P + R) := by
    intro he
    rcases (affineX_eq_iff hP hE).mp he with hs | hn
    · apply hR
      exact add_left_cancel (show P + R = P + 0 by simpa using hs.symm)
    · apply hF
      have hh := (eq_neg_iff_add_eq_zero).mp hn
      simpa only [add_assoc] using hh
  exact normalizedSlope_diagonal_generic hP hR hD hE hF hxD hxE

end TRR08Geometry

#print axioms TRR08Geometry.normalizedSlope_of_add_eq_zero
#print axioms TRR08Geometry.normalizedSlope_diagonal
