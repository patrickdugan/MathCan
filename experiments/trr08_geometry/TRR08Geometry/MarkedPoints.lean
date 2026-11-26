module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Actual marked points supplying the nine distinct roots in TRR-08

This module uses Mathlib's nonsingular affine Weierstrass points and their
proved group law. The order condition is `19 ≤ addOrderOf T`; it therefore
requires a finite-order marked point and includes every exact prime order
at least nineteen. No residue theorem or local expansion is assumed or
claimed here.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type*} [Field K] {W : Affine K}

/-- The affine x-coordinate, with zero assigned at the identity. -/
def affineX : W.Point → K
  | .zero => 0
  | .some x _ _ => x

/-- The affine y-coordinate, with zero assigned at the identity. -/
def affineY : W.Point → K
  | .zero => 0
  | .some _ y _ => y

@[simp] theorem affineX_some {x y : K} (h : W.Nonsingular x y) :
    affineX (.some x y h) = x := rfl

@[simp] theorem affineY_some {x y : K} (h : W.Nonsingular x y) :
    affineY (.some x y h) = y := rfl

/-- Away from the identity, x identifies exactly a point and its negative. -/
theorem affineX_eq_iff {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    affineX P = affineX Q ↔ P = Q ∨ P = -Q := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
    cases Q with
    | zero => exact (hQ rfl).elim
    | some u v hu => exact Affine.Point.X_eq_iff

variable [DecidableEq K]

/-- The first nine positive multiples of the marked point. -/
def firstNine (T : W.Point) (i : Fin 9) : W.Point := (i.val + 1) • T

theorem firstNine_ne_zero (T : W.Point) (hT : 19 ≤ addOrderOf T) (i : Fin 9) :
    firstNine T i ≠ 0 := by
  intro hz
  have hle := addOrderOf_le_of_nsmul_eq_zero (by omega : 0 < i.val + 1) hz
  have hi := i.isLt
  omega

theorem firstNine_injective (T : W.Point) (hT : 19 ≤ addOrderOf T) :
    Function.Injective (firstNine T) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hi' : i.val + 1 < addOrderOf T := by omega
  have hj' : j.val + 1 < addOrderOf T := by omega
  have h := nsmul_injOn_Iio_addOrderOf hi' hj' hij
  exact Fin.ext (by omega)

theorem firstNine_ne_neg (T : W.Point) (hT : 19 ≤ addOrderOf T) (i j : Fin 9) :
    firstNine T i ≠ -firstNine T j := by
  intro hij
  have hz : ((i.val + 1) + (j.val + 1)) • T = 0 := by
    rw [add_nsmul]
    change firstNine T i + firstNine T j = 0
    rw [hij]
    exact neg_add_cancel _
  have hle := addOrderOf_le_of_nsmul_eq_zero
    (by omega : 0 < (i.val + 1) + (j.val + 1)) hz
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- These are the actual nine distinct field elements needed by the
    degree-eight root bound. -/
theorem firstNine_x_injective (T : W.Point) (hT : 19 ≤ addOrderOf T) :
    Function.Injective (fun i : Fin 9 => affineX (firstNine T i)) := by
  intro i j hij
  rcases (affineX_eq_iff (firstNine_ne_zero T hT i)
    (firstNine_ne_zero T hT j)).mp hij with hsame | hneg
  · exact firstNine_injective T hT hsame
  · exact (firstNine_ne_neg T hT i j hneg).elim

/-- The tangent denominator vanishes only at a point whose double is zero. -/
theorem tangent_denominator_ne_zero {P : W.Point} (hP : P ≠ 0)
    (hdouble : P + P ≠ 0) :
    2 * affineY P + W.a₁ * affineX P + W.a₃ ≠ 0 := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
    intro hz
    have hneg : y = W.negY x y := by
      simp only [affineX_some, affineY_some] at hz
      dsimp [Affine.negY]
      linear_combination hz
    exact hdouble (Affine.Point.add_self_of_Y_eq hneg)

theorem firstNine_tangent_denominator_ne_zero (T : W.Point)
    (hT : 19 ≤ addOrderOf T) (i : Fin 9) :
    2 * affineY (firstNine T i) + W.a₁ * affineX (firstNine T i) + W.a₃ ≠ 0 := by
  apply tangent_denominator_ne_zero (firstNine_ne_zero T hT i)
  intro hz
  have heq : firstNine T i = -firstNine T i := (eq_neg_iff_add_eq_zero).2 hz
  exact firstNine_ne_neg T hT i i heq

section ShortModel

variable [W.IsShortNF]

omit [DecidableEq K] in
/-- Mathlib's ellipticity hypothesis supplies the nonzero discriminant used
    by the scalar coefficient contradiction. -/
theorem short_discriminant_ne_zero [W.IsElliptic] :
    (4 : K) * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 ≠ 0 := by
  intro hz
  apply W.isUnit_Δ.ne_zero
  rw [W.Δ_of_isShortNF, hz, mul_zero]

omit [DecidableEq K] in
/-- Actual nonidentity points satisfy the short Weierstrass equation. -/
theorem short_curve_equation {P : W.Point} (hP : P ≠ 0) :
    affineY P ^ 2 = affineX P ^ 3 + W.a₄ * affineX P + W.a₆ := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
    have heq := (Affine.equation_iff ..).mp h.1
    simpa [affineX, affineY, W.a₁_of_isShortNF, W.a₂_of_isShortNF,
      W.a₃_of_isShortNF] using heq

theorem short_y_ne_zero {P : W.Point} (hP : P ≠ 0) (hdouble : P + P ≠ 0) :
    affineY P ≠ 0 := by
  have h := tangent_denominator_ne_zero hP hdouble
  intro hy
  apply h
  simp [hy]

/-- This equation is derived from Mathlib's actual point-addition definition. -/
theorem short_doubling_x {P : W.Point} (hP : P ≠ 0) (hdouble : P + P ≠ 0) :
    affineX (P + P) =
      ((3 * affineX P ^ 2 + W.a₄) / (2 * affineY P)) ^ 2 - 2 * affineX P := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
    have hn : y ≠ W.negY x y := by
      intro hy
      exact hdouble (Affine.Point.add_self_of_Y_eq hy)
    rw [Affine.Point.add_self_of_Y_ne hn]
    simp only [affineX_some, affineY_some, Affine.addX,
      Affine.slope_of_Y_ne rfl hn]
    simp only [W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF,
      Affine.negY, mul_zero, zero_mul, add_zero, sub_zero,
      sub_neg_eq_add]
    rw [← two_mul y]
    ring

end ShortModel

end TRR08Geometry

#print axioms TRR08Geometry.affineX_eq_iff
#print axioms TRR08Geometry.firstNine_ne_zero
#print axioms TRR08Geometry.firstNine_injective
#print axioms TRR08Geometry.firstNine_ne_neg
#print axioms TRR08Geometry.firstNine_x_injective
#print axioms TRR08Geometry.tangent_denominator_ne_zero
#print axioms TRR08Geometry.firstNine_tangent_denominator_ne_zero
#print axioms TRR08Geometry.short_curve_equation
#print axioms TRR08Geometry.short_discriminant_ne_zero
#print axioms TRR08Geometry.short_y_ne_zero
#print axioms TRR08Geometry.short_doubling_x
