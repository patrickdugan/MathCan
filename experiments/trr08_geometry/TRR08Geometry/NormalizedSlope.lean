module

public import TRR08Geometry.MarkedPoints
public import Mathlib.Tactic.FieldSimp

/-!
# Normalized chord and tangent slopes

The value at an identity or inverse pair is zero. All other values are
Mathlib's actual chord or tangent slope. The finite averaging argument uses
the diagonal cocycle proved from these coordinate formulas.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K}

/-- The chord/tangent slope, extended by zero at identity and inverse pairs. -/
def normalizedSlope : W.Point → W.Point → K
  | .zero, _ => 0
  | _, .zero => 0
  | .some x y _, .some u v _ => W.slope x u y v

@[simp] theorem normalizedSlope_zero_left (P : W.Point) :
    normalizedSlope (0 : W.Point) P = 0 := by cases P <;> rfl

@[simp] theorem normalizedSlope_zero_right (P : W.Point) :
    normalizedSlope P (0 : W.Point) = 0 := by cases P <;> rfl

@[simp] theorem normalizedSlope_neg_right (P : W.Point) :
    normalizedSlope P (-P) = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [Affine.Point.neg_some, normalizedSlope]
      exact Affine.slope_of_Y_eq rfl (W.negY_negY x y).symm

@[simp] theorem normalizedSlope_neg_left (P : W.Point) :
    normalizedSlope (-P) P = 0 := by
  simpa only [neg_neg] using normalizedSlope_neg_right (-P)

theorem normalizedSlope_of_x_ne {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : affineX P ≠ affineX Q) :
    normalizedSlope P Q = (affineY P - affineY Q) / (affineX P - affineX Q) := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
      cases Q with
      | zero => exact (hQ rfl).elim
      | some u v hu => exact Affine.slope_of_X_ne hx

theorem normalizedSlope_comm (P Q : W.Point) :
    normalizedSlope P Q = normalizedSlope Q P := by
  by_cases hP : P = 0
  · subst P; simp
  by_cases hQ : Q = 0
  · subst Q; simp
  by_cases hx : affineX P = affineX Q
  · rcases (affineX_eq_iff hP hQ).mp hx with hsame | hneg
    · subst P; rfl
    · subst P; simp
  · rw [normalizedSlope_of_x_ne hP hQ hx,
      normalizedSlope_of_x_ne hQ hP (Ne.symm hx)]
    apply (div_eq_div_iff (sub_ne_zero.mpr hx) (sub_ne_zero.mpr (Ne.symm hx))).mpr
    ring

section ShortModel

variable [W.IsShortNF]

omit [DecidableEq K] [W.IsShortNF] in
@[simp] theorem affineX_neg (P : W.Point) : affineX (-P) = affineX P := by
  cases P <;> rfl

omit [DecidableEq K] in
@[simp] theorem affineY_neg (P : W.Point) : affineY (-P) = -affineY P := by
  cases P with
  | zero => change (0 : K) = -0; simp
  | some x y h => simp [Affine.Point.neg_some, affineY, Affine.negY]

theorem normalizedSlope_self {P : W.Point} (hP : P ≠ 0) (hdouble : P + P ≠ 0) :
    normalizedSlope P P = (3 * affineX P ^ 2 + W.a₄) / (2 * affineY P) := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
      have hn : y ≠ W.negY x y := fun hy => hdouble (Affine.Point.add_self_of_Y_eq hy)
      simp only [normalizedSlope, affineX_some, affineY_some, Affine.slope_of_Y_ne rfl hn]
      simp only [W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF,
        Affine.negY, mul_zero, zero_mul, add_zero, sub_zero, sub_neg_eq_add]
      rw [← two_mul y]

theorem normalizedSlope_add_x {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hadd : P + Q ≠ 0) :
    affineX (P + Q) = normalizedSlope P Q ^ 2 - affineX P - affineX Q := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
      cases Q with
      | zero => exact (hQ rfl).elim
      | some u v hu =>
          have hxy : ¬ (x = u ∧ y = W.negY u v) := by
            rintro ⟨hx, hy⟩
            exact hadd (Affine.Point.add_of_Y_eq hx hy)
          rw [Affine.Point.add_some hxy]
          simp [affineX, normalizedSlope, Affine.addX]

theorem normalizedSlope_add_y {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hadd : P + Q ≠ 0) :
    affineY (P + Q) = -affineY P +
      normalizedSlope P Q * (affineX P - affineX (P + Q)) := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
      cases Q with
      | zero => exact (hQ rfl).elim
      | some u v hu =>
          have hxy : ¬ (x = u ∧ y = W.negY u v) := by
            rintro ⟨hx, hy⟩
            exact hadd (Affine.Point.add_of_Y_eq hx hy)
          rw [Affine.Point.add_some hxy]
          simp only [affineY_some, affineX_some, normalizedSlope,
            Affine.addY, Affine.negY, Affine.negAddY, W.a₁_of_isShortNF,
            W.a₃_of_isShortNF, zero_mul, sub_zero]
          ring

omit [W.IsShortNF] in
/-- The chord incidence equation also holds at a tangent pair. -/
theorem normalizedSlope_line {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hadd : P + Q ≠ 0) :
    (affineX P - affineX Q) * normalizedSlope P Q = affineY P - affineY Q := by
  by_cases hx : affineX P = affineX Q
  · rcases (affineX_eq_iff hP hQ).mp hx with hs | hn
    · subst P; ring
    · exact (hadd (by rw [hn]; exact neg_add_cancel Q)).elim
  · rw [normalizedSlope_of_x_ne hP hQ hx]
    field_simp

/-- The divided cubic equation, including its tangent specialization. -/
theorem normalizedSlope_chord {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hadd : P + Q ≠ 0) :
    (affineX P - affineX Q) * normalizedSlope P Q ^ 2 +
      2 * affineY Q * normalizedSlope P Q =
      affineX P ^ 2 + affineX P * affineX Q + affineX Q ^ 2 + W.a₄ := by
  by_cases hx : affineX P = affineX Q
  · rcases (affineX_eq_iff hP hQ).mp hx with hs | hn
    · subst P
      have hden := tangent_denominator_ne_zero hQ hadd
      simp only [W.a₁_of_isShortNF, W.a₃_of_isShortNF, zero_mul, add_zero] at hden
      rw [normalizedSlope_self hQ hadd]
      simp only [sub_self, zero_mul, zero_add]
      rw [mul_div_cancel₀ _ hden]
      ring
    · exact (hadd (by rw [hn]; exact neg_add_cancel Q)).elim
  · have hl := normalizedSlope_line hP hQ hadd
    have hp := short_curve_equation hP
    have hq := short_curve_equation hQ
    have hy : affineY P = affineY Q +
        (affineX P - affineX Q) * normalizedSlope P Q := by linear_combination -hl
    rw [hy] at hp
    have hf : (affineX P - affineX Q) *
        ((affineX P - affineX Q) * normalizedSlope P Q ^ 2 +
          2 * affineY Q * normalizedSlope P Q -
          (affineX P ^ 2 + affineX P * affineX Q + affineX Q ^ 2 + W.a₄)) = 0 := by
      linear_combination hp - hq
    have hz := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hx)
    linear_combination hz

theorem normalizedSlope_neg_both (P Q : W.Point) :
    normalizedSlope (-P) (-Q) = -normalizedSlope P Q := by
  by_cases hP : P = 0
  · subst P; simp
  by_cases hQ : Q = 0
  · subst Q; simp
  by_cases hx : affineX P = affineX Q
  · rcases (affineX_eq_iff hP hQ).mp hx with hs | hn
    · subst Q
      by_cases hd : P + P = 0
      · have he : P = -P := (eq_neg_iff_add_eq_zero).mpr hd
        have hz : normalizedSlope P P = 0 := by
          calc
            normalizedSlope P P = normalizedSlope P (-P) := congrArg (normalizedSlope P) he
            _ = 0 := normalizedSlope_neg_right P
        have hneg : normalizedSlope (-P) (-P) = 0 := by rw [← he]; exact hz
        rw [hneg, hz, neg_zero]
      · have hnd : -P + -P ≠ 0 := by simpa only [← neg_add, neg_ne_zero] using hd
        rw [normalizedSlope_self (neg_ne_zero.mpr hP) hnd,
          normalizedSlope_self hP hd, affineX_neg, affineY_neg]
        simp only [mul_neg, div_neg]
    · subst P; simp
  · rw [normalizedSlope_of_x_ne (neg_ne_zero.mpr hP) (neg_ne_zero.mpr hQ)
        (by simpa only [affineX_neg] using hx), normalizedSlope_of_x_ne hP hQ hx]
    simp only [affineX_neg, affineY_neg]
    rw [show -affineY P - -affineY Q = -(affineY P-affineY Q) by ring, neg_div]

/-- Rotating the three intersections of one chord preserves its slope. -/
theorem normalizedSlope_rotate {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hadd : P + Q ≠ 0) :
    normalizedSlope P Q = normalizedSlope Q (-(P + Q)) := by
  have hxadd := normalizedSlope_add_x hP hQ hadd
  have hyadd := normalizedSlope_add_y hQ hP (by simpa only [add_comm] using hadd)
  rw [add_comm Q P, normalizedSlope_comm Q P] at hyadd
  by_cases hx : affineX Q = affineX (P + Q)
  · have hDQ : P + Q ≠ Q := by
      intro he
      exact hP (add_right_cancel (show P + Q = 0 + Q by simpa using he))
    have hneg : Q = -(P + Q) := ((affineX_eq_iff hQ hadd).mp hx).resolve_left
      (fun he => hDQ he.symm)
    have hdouble : Q + Q ≠ 0 := by
      intro hz
      have he : Q = -Q := (eq_neg_iff_add_eq_zero).mpr hz
      have hsum : P + Q = Q := by
        have hh := congrArg Neg.neg hneg
        simpa only [neg_neg, ← he] using hh.symm
      exact hDQ hsum
    have hc := normalizedSlope_chord hP hQ hadd
    have ht : 2 * affineY Q * normalizedSlope P Q = 3 * affineX Q ^ 2 + W.a₄ := by
      linear_combination hc + (affineX P - affineX Q) * (hx.trans hxadd)
    rw [← hneg, normalizedSlope_self hQ hdouble]
    apply (eq_div_iff ?_).mpr
    · simpa only [mul_comm] using ht
    · have hh := tangent_denominator_ne_zero hQ hdouble
      simpa only [W.a₁_of_isShortNF, W.a₃_of_isShortNF, zero_mul, add_zero] using hh
  · rw [normalizedSlope_of_x_ne hQ (neg_ne_zero.mpr hadd)
      (by simpa only [affineX_neg] using hx), affineX_neg, affineY_neg]
    apply (eq_div_iff (sub_ne_zero.mpr hx)).mpr
    linear_combination -hyadd

/-- The chord through a sum and the negative of one summand has opposite slope. -/
theorem normalizedSlope_sum_neg {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hadd : P + Q ≠ 0) :
    normalizedSlope (P + Q) (-Q) = -normalizedSlope P Q := by
  have h := normalizedSlope_rotate (neg_ne_zero.mpr hP) (neg_ne_zero.mpr hQ)
    (by simpa only [← neg_add, neg_ne_zero] using hadd)
  rw [normalizedSlope_neg_both, ← neg_add, neg_neg, normalizedSlope_comm (-Q) (P + Q)] at h
  exact h.symm

omit [DecidableEq K] in
private theorem diagonal_slope_algebra (x y z w A m n p q : K)
    (ht : 2*y*m = 3*x^2+A)
    (hc : (z-x)*n^2+2*y*n = z^2+z*x+x^2+A)
    (hl : w = y+n*(z-x))
    (hp : (m^2-2*x-z)*p = -y+m*(3*x-m^2)-w)
    (hq : (2*x+z-n^2)*q = 2*y-n*(2*x+z-n^2))
    (hd₁ : m^2-2*x-z ≠ 0) (hd₂ : 2*x+z-n^2 ≠ 0) :
    m+p = n+q := by
  have hzero : (m^2-2*x-z)*(2*x+z-n^2)*(m+p-n-q) = 0 := by
    linear_combination (2*x+z-n^2)*hp - (m^2-2*x-z)*hq -
      (2*x+z-n^2)*hl + (m+n)*(hc-ht)
  have hz := (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hd₁ hd₂)
  linear_combination hz

omit [DecidableEq K] in
private theorem double_tangent_algebra (x y z w A m n p q : K)
    (hz : z = m^2-2*x) (hw : w = -y+m*(x-z))
    (ht : 2*y*m = 3*x^2+A) (htd : 2*w*p = 3*z^2+A)
    (hn : (x-z)*n = y-w)
    (hq : (2*x+z-n^2)*q = 2*y-n*(2*x+z-n^2))
    (hx : x-z ≠ 0) (hd : 2*x+z-n^2 ≠ 0) :
    m+p = n+q := by
  have hmn : (m-n)*(x-z) = 2*w := by linear_combination -hw-hn
  have hid : 2*w*(m+p) = (x-z)^2 := by
    linear_combination htd + 2*m*hw - ht - 2*(x-z)*hz
  have hprod : ((m-n)*(m+p)-(x-z))*(x-z) = 0 := by
    linear_combination (m+p)*hmn+hid
  have hc := (mul_eq_zero.mp hprod).resolve_right hx
  have hs : (m+n)*(x-z) = 2*y := by linear_combination -hw+hn
  have hzero : (2*x+z-n^2)*(m+p-n-q) = 0 := by
    linear_combination (m+n)*hc+hs+(m+p)*hz-hq
  have hh := (mul_eq_zero.mp hzero).resolve_left hd
  linear_combination hh

/-- The diagonal slope identity when the two outer lines are secants. -/
theorem normalizedSlope_diagonal_generic {P R : W.Point}
    (hP : P ≠ 0) (hR : R ≠ 0) (hD : P+P ≠ 0)
    (hE : P+R ≠ 0) (hF : (P+P)+R ≠ 0)
    (hxD : affineX (P+P) ≠ affineX R)
    (hxE : affineX P ≠ affineX (P+R)) :
    normalizedSlope P P + normalizedSlope (P+P) R =
      normalizedSlope P R + normalizedSlope P (P+R) := by
  let x := affineX P
  let y := affineY P
  let z := affineX R
  let w := affineY R
  let m := normalizedSlope P P
  let n := normalizedSlope P R
  let p := normalizedSlope (P+P) R
  let q := normalizedSlope P (P+R)
  have hdX : affineX (P+P) = m^2-2*x := by
    have hh := normalizedSlope_add_x hP hP hD
    change affineX (P+P) = m^2-x-x at hh
    linear_combination hh
  have hdY : affineY (P+P) = -y+m*(3*x-m^2) := by
    have hh := normalizedSlope_add_y hP hP hD
    change affineY (P+P) = -y+m*(x-affineX (P+P)) at hh
    rw [hdX] at hh
    linear_combination hh
  have heX : affineX (P+R) = n^2-x-z := normalizedSlope_add_x hP hR hE
  have heY : affineY (P+R) = -y+n*(2*x+z-n^2) := by
    have hh := normalizedSlope_add_y hP hR hE
    change affineY (P+R) = -y+n*(x-affineX (P+R)) at hh
    rw [heX] at hh
    linear_combination hh
  apply diagonal_slope_algebra x y z w W.a₄ m n p q
  · have hh := normalizedSlope_chord hP hP hD
    change (x-x)*m^2+2*y*m = x^2+x*x+x^2+W.a₄ at hh
    linear_combination hh
  · have hh := normalizedSlope_chord hR hP (by simpa only [add_comm] using hE)
    rw [normalizedSlope_comm R P] at hh
    exact hh
  · have hh := normalizedSlope_line hP hR hE
    change (x-z)*n = y-w at hh
    linear_combination hh
  · have hh := normalizedSlope_line hD hR hF
    change (affineX (P+P)-z)*p = affineY (P+P)-w at hh
    rwa [hdX, hdY] at hh
  · have hh := normalizedSlope_line hP hE (by simpa only [add_assoc] using hF)
    change (x-affineX (P+R))*q = y-affineY (P+R) at hh
    rw [heX, heY] at hh
    linear_combination hh
  · have hh := sub_ne_zero.mpr hxD
    change affineX (P+P)-z ≠ 0 at hh
    rwa [hdX] at hh
  · have hh := sub_ne_zero.mpr hxE
    change x-affineX (P+R) ≠ 0 at hh
    rw [heX] at hh
    intro hz
    apply hh
    linear_combination hz

/-- The sole outer-tangent specialization in the diagonal argument. -/
theorem normalizedSlope_diagonal_double {P : W.Point}
    (hP : P ≠ 0) (hD : P+P ≠ 0)
    (hE : P+(P+P) ≠ 0) (hF : (P+P)+(P+P) ≠ 0) :
    normalizedSlope P P + normalizedSlope (P+P) (P+P) =
      normalizedSlope P (P+P) + normalizedSlope P (P+(P+P)) := by
  let x := affineX P
  let y := affineY P
  let z := affineX (P+P)
  let w := affineY (P+P)
  let m := normalizedSlope P P
  let n := normalizedSlope P (P+P)
  let p := normalizedSlope (P+P) (P+P)
  let q := normalizedSlope P (P+(P+P))
  have hz : z = m^2-2*x := by
    have hh := normalizedSlope_add_x hP hP hD
    change z = m^2-x-x at hh
    linear_combination hh
  have hw : w = -y+m*(x-z) := normalizedSlope_add_y hP hP hD
  have heX : affineX (P+(P+P)) = n^2-x-z := normalizedSlope_add_x hP hD hE
  have heY : affineY (P+(P+P)) = -y+n*(2*x+z-n^2) := by
    have hh := normalizedSlope_add_y hP hD hE
    change affineY (P+(P+P)) = -y+n*(x-affineX (P+(P+P))) at hh
    rw [heX] at hh
    linear_combination hh
  apply double_tangent_algebra x y z w W.a₄ m n p q hz hw
  · have hh := normalizedSlope_chord hP hP hD
    change (x-x)*m^2+2*y*m = x^2+x*x+x^2+W.a₄ at hh
    linear_combination hh
  · have hh := normalizedSlope_chord hD hD hF
    change (z-z)*p^2+2*w*p = z^2+z*z+z^2+W.a₄ at hh
    linear_combination hh
  · exact normalizedSlope_line hP hD hE
  · have hh := normalizedSlope_line hP hE (by simpa only [add_assoc] using hF)
    change (x-affineX (P+(P+P)))*q = y-affineY (P+(P+P)) at hh
    rw [heX, heY] at hh
    linear_combination hh
  · apply sub_ne_zero.mpr
    intro he
    rcases (affineX_eq_iff hP hD).mp he with hs | hn
    · exact hP (add_left_cancel (show P+P = P+0 by simpa using hs.symm))
    · exact hE ((eq_neg_iff_add_eq_zero).mp hn)
  · have hx : affineX P ≠ affineX (P+(P+P)) := by
      intro he
      rcases (affineX_eq_iff hP hE).mp he with hs | hn
      · exact hD (add_left_cancel (show P+(P+P) = P+0 by simpa using hs.symm))
      · apply hF
        have hh := (eq_neg_iff_add_eq_zero).mp hn
        simpa only [add_assoc] using hh
    intro he
    apply (sub_ne_zero.mpr hx)
    change x-affineX (P+(P+P)) = 0
    rw [heX]
    linear_combination he

end ShortModel

end TRR08Geometry

#print axioms TRR08Geometry.normalizedSlope_of_x_ne
#print axioms TRR08Geometry.normalizedSlope_comm
#print axioms TRR08Geometry.affineX_neg
#print axioms TRR08Geometry.affineY_neg
#print axioms TRR08Geometry.normalizedSlope_self
#print axioms TRR08Geometry.normalizedSlope_add_x
#print axioms TRR08Geometry.normalizedSlope_add_y
#print axioms TRR08Geometry.normalizedSlope_line
#print axioms TRR08Geometry.normalizedSlope_chord
#print axioms TRR08Geometry.normalizedSlope_neg_both
#print axioms TRR08Geometry.normalizedSlope_rotate
#print axioms TRR08Geometry.normalizedSlope_sum_neg
#print axioms TRR08Geometry.normalizedSlope_diagonal_generic
#print axioms TRR08Geometry.normalizedSlope_diagonal_double
