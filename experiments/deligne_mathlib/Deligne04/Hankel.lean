import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
DEL-04: generic exact Hankel/Vandermonde factorization.

This file proves characteristic-independent algebraic identities for
the moments tₙ = ∑ⱼ wⱼ λⱼⁿ over any commutative ring. It does not claim
a spectral-radius estimate or Deligne's weight theorem.
-/

open scoped BigOperators Matrix
open Finset

namespace Deligne04

variable {R : Type*} [CommRing R] {s : ℕ}

/-- Weighted power trace, with aggregated eigenvalue weights. -/
def powerTrace (lam weights : Fin s → R) (n : ℕ) : R :=
  ∑ j : Fin s, weights j * lam j ^ n

/-- The Hankel factorization Vᵀ diag(wⱼ λⱼ) V, with
Vᵢⱼ = λᵢʲ. -/
def hankel (lam weights : Fin s → R) : Matrix (Fin s) (Fin s) R :=
  (Matrix.vandermonde lam)ᵀ *
    Matrix.diagonal (fun j => weights j * lam j) *
      Matrix.vandermonde lam

/-- Every entry is the intended power sum t_(i+j+1). -/
theorem hankel_entry (lam weights : Fin s → R) (i j : Fin s) :
    hankel lam weights i j = powerTrace lam weights (i.val + j.val + 1) := by
  rw [hankel, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    Matrix.vandermonde_apply, powerTrace]
  apply Finset.sum_congr rfl
  intro k _
  simp only [pow_add, pow_one]
  ring

/-- General determinant identity from Vᵀ D V. -/
theorem hankel_det (lam weights : Fin s → R) :
    (hankel lam weights).det =
      (∏ j : Fin s, weights j * lam j) *
        (Matrix.vandermonde lam).det ^ 2 := by
  simp only [hankel, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  ring

/-- Explicit discriminant-style determinant product. -/
theorem hankel_det_product (lam weights : Fin s → R) :
    (hankel lam weights).det =
      (∏ j : Fin s, weights j * lam j) *
        (∏ i : Fin s, ∏ j ∈ Finset.Ioi i, (lam j - lam i)) ^ 2 := by
  rw [hankel_det, Matrix.det_vandermonde]

/-- The genuine nonzero poles and distinct eigenvalues make
the Hankel matrix nonsingular, over an integral domain. -/
theorem hankel_det_ne_zero
    [IsDomain R] (lam weights : Fin s → R)
    (hinj : Function.Injective lam)
    (hlam : ∀ j, lam j ≠ 0)
    (hweights : ∀ j, weights j ≠ 0) :
    (hankel lam weights).det ≠ 0 := by
  rw [hankel_det]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact mul_ne_zero (hweights j) (hlam j)
  · exact pow_ne_zero 2
      (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)

#print axioms hankel_entry
#print axioms hankel_det
#print axioms hankel_det_product
#print axioms hankel_det_ne_zero

end Deligne04
