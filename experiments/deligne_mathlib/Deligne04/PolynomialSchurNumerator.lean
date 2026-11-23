import Deligne04.RankDPivotInterpolation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# DEL-22E: bordered Jacobian minors and the polynomial Schur numerator

For an arbitrary commutative coefficient ring, the adjugate numerator
Δv - C adj(H) B is defined even where Δ=det(H) is a zero divisor.

On an invertible-pivot chart, Schur's determinant identity identifies
this genuine polynomial expression with the determinant of the bordered
matrix. The identity does not divide by Δ.

The original DEL-16 Jacobian and universal sections will be plugged
into this ring-generic algebraic lemma in a separate module.
-/

open scoped Matrix BigOperators

namespace Deligne22E

/-- The d×1 column added to the original Jacobian pivot. -/
def rightBlock {R : Type*} [CommRing R] {d : ℕ}
    (b : Fin d → R) : Matrix (Fin d) (Fin 1) R :=
  fun i _ => b i

/-- The 1×d section-gradient row at the pivot coordinates. -/
def bottomBlock {R : Type*} [CommRing R] {d : ℕ}
    (c : Fin d → R) : Matrix (Fin 1) (Fin d) R :=
  fun _ i => c i

/-- The lower right corner of the bordered matrix. -/
def cornerBlock {R : Type*} [CommRing R]
    (v : R) : Matrix (Fin 1) (Fin 1) R :=
  fun _ _ => v

/-- A bordered pivot determinant, in the original coefficient ring. -/
noncomputable def borderedPivot {R : Type*} [CommRing R] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) R) (b c : Fin d → R) (v : R) :
    Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) R :=
  Matrix.fromBlocks H (rightBlock b) (bottomBlock c) (cornerBlock v)

/-- The numerator has polynomial entries and involves no inverse:
Δv - C adj(H) B. This is meaningful over nonreduced rings as well. -/
noncomputable def pivotNumerator {R : Type*} [CommRing R] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) R) (b c : Fin d → R) (v : R) : R :=
  H.det * v - (bottomBlock c * H.adjugate * rightBlock b) 0 0

/-- The bordered determinant equals its polynomial Schur numerator
in any commutative ring where the pivot matrix is invertible.
In particular, this applies to the original scheme coordinate ring
localized at Δ, including nonreduced rings. -/
theorem det_borderedPivot_eq_numerator_of_invertible
    {R : Type*} [CommRing R] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) R) (b c : Fin d → R) (v : R)
    [Invertible H] :
    (borderedPivot H b c v).det = pivotNumerator H b c v := by
  classical
  letI : Invertible H.det := Matrix.detInvertibleOfInvertible H
  have hmul :
      (bottomBlock c * ⅟H * rightBlock b) 0 0 =
        ⅟H.det * (bottomBlock c * H.adjugate * rightBlock b) 0 0 := by
    rw [Matrix.invOf_eq H]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  unfold borderedPivot pivotNumerator
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_fin_one]
  change H.det * (v - (bottomBlock c * ⅟H * rightBlock b) 0 0) =
    H.det * v - (bottomBlock c * H.adjugate * rightBlock b) 0 0
  rw [hmul, mul_sub, ← mul_assoc, mul_invOf_self, one_mul]

/-- A unit determinant suffices to make the pivot invertible.
This form is convenient for chart localization. -/
theorem det_borderedPivot_eq_numerator_of_unit
    {R : Type*} [CommRing R] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) R) (b c : Fin d → R) (v : R)
    (hunit : IsUnit H.det) :
    (borderedPivot H b c v).det = pivotNumerator H b c v := by
  classical
  obtain ⟨inst⟩ := hunit.nonempty_invertible
  letI : Invertible H.det := inst
  letI : Invertible H := Matrix.invertibleOfDetInvertible H
  exact det_borderedPivot_eq_numerator_of_invertible H b c v

/-- Over a field, a nonzero original pivot supplies the chart formula. -/
theorem det_borderedPivot_eq_numerator_of_det_ne_zero
    {L : Type*} [Field L] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) L) (b c : Fin d → L) (v : L)
    (hdet : H.det ≠ 0) :
    (borderedPivot H b c v).det = pivotNumerator H b c v :=
  det_borderedPivot_eq_numerator_of_unit H b c v
    (isUnit_iff_ne_zero.mpr hdet)

#print axioms det_borderedPivot_eq_numerator_of_invertible
#print axioms det_borderedPivot_eq_numerator_of_unit
#print axioms det_borderedPivot_eq_numerator_of_det_ne_zero

end Deligne22E
