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

/-- The bordered pivot itself commutes with every ring homomorphism.
This will transport actual polynomial minors to geometric field points
and universal parameters to their fixed specializations. -/
theorem borderedPivot_map
    {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}
    (φ : R →+* S) (H : Matrix (Fin d) (Fin d) R)
    (b c : Fin d → R) (v : R) :
    (borderedPivot H b c v).map φ =
      borderedPivot (H.map φ) (fun i => φ (b i))
        (fun i => φ (c i)) (φ v) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- The unlocalized polynomial Schur numerator commutes exactly with
coefficient and geometric-point specialization. The adjugate,
determinant, and matrix products all commute with ring maps. -/
theorem pivotNumerator_map
    {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}
    (φ : R →+* S) (H : Matrix (Fin d) (Fin d) R)
    (b c : Fin d → R) (v : R) :
    φ (pivotNumerator H b c v) =
      pivotNumerator (H.map φ) (fun i => φ (b i))
        (fun i => φ (c i)) (φ v) := by
  classical
  have hbot : (bottomBlock c).map φ =
      bottomBlock (fun i => φ (c i)) := by
    ext i j
    rfl
  have hright : (rightBlock b).map φ =
      rightBlock (fun i => φ (b i)) := by
    ext i j
    rfl
  have hadj : (H.adjugate).map φ = (H.map φ).adjugate :=
    φ.map_adjugate H
  have hprod :
      φ ((bottomBlock c * H.adjugate * rightBlock b) 0 0) =
      (bottomBlock (fun i => φ (c i)) *
        (H.map φ).adjugate * rightBlock (fun i => φ (b i))) 0 0 := by
    change ((bottomBlock c * H.adjugate * rightBlock b).map φ) 0 0 = _
    rw [Matrix.map_mul, Matrix.map_mul, hbot, hright, hadj]
  unfold pivotNumerator
  rw [map_sub, map_mul, RingHom.map_det, hprod]
  have hmatrix : φ.mapMatrix H = H.map φ := by
    ext i j
    rfl
  rw [hmatrix]

/-- The determinant polynomial of a bordered pivot also specializes
exactly, even at singular pivots. -/
theorem det_borderedPivot_map
    {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}
    (φ : R →+* S) (H : Matrix (Fin d) (Fin d) R)
    (b c : Fin d → R) (v : R) :
    φ (borderedPivot H b c v).det =
      (borderedPivot (H.map φ) (fun i => φ (b i))
        (fun i => φ (c i)) (φ v)).det := by
  rw [RingHom.map_det]
  have hmatrix :
      φ.mapMatrix (borderedPivot H b c v) =
        (borderedPivot H b c v).map φ := by
    ext i j
    rfl
  rw [hmatrix, borderedPivot_map]

/-- Over a field, the Schur complement evaluates the bordered
determinant as a nonzero pivot determinant times the residual.
This is the pointwise form of the localized polynomial identity. -/
theorem det_borderedPivot_eq_schur_field
    {L : Type*} [Field L] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) L) (b c : Fin d → L) (v : L)
    (hdet : H.det ≠ 0) :
    (borderedPivot H b c v).det =
      H.det * (v - (bottomBlock c * H⁻¹ * rightBlock b) 0 0) := by
  classical
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨inst⟩ := hu.nonempty_invertible
  letI : Invertible H.det := inst
  letI : Invertible H := Matrix.invertibleOfDetInvertible H
  unfold borderedPivot
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_fin_one]
  rw [Matrix.invOf_eq_nonsing_inv]
  rfl

/-- A bordered determinant vanishes exactly when the new row is
interpolated by the original pivot rows. This is valid for d=0. -/
theorem det_borderedPivot_zero_iff_interpolation
    {L : Type*} [Field L] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) L) (b c : Fin d → L) (v : L)
    (hdet : H.det ≠ 0) :
    (borderedPivot H b c v).det = 0 ↔
      v = ∑ t : Fin d, (c ᵥ* H⁻¹) t * b t := by
  classical
  have hsum :
      (bottomBlock c * H⁻¹ * rightBlock b) 0 0 =
        ∑ t : Fin d, (c ᵥ* H⁻¹) t * b t := by
    simp only [Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      bottomBlock, rightBlock]
  rw [det_borderedPivot_eq_schur_field H b c v hdet, hsum, mul_eq_zero]
  simp only [hdet, false_or, sub_eq_zero]

#print axioms det_borderedPivot_eq_numerator_of_invertible
#print axioms det_borderedPivot_eq_numerator_of_unit
#print axioms det_borderedPivot_eq_numerator_of_det_ne_zero
#print axioms borderedPivot_map
#print axioms pivotNumerator_map
#print axioms det_borderedPivot_map
#print axioms det_borderedPivot_eq_schur_field
#print axioms det_borderedPivot_zero_iff_interpolation

end Deligne22E
