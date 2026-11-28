import Deligne04.TensorSpectrum
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.Tactic

/-!
# DEL-06: a tensor eigenvector for arbitrary complex Frobenius matrices

This model works for nonsemisimple operators. It represents a k-fold
tensor of the free module (Fin n -> C) by functions Fin k -> Fin n.
The tensor operator has entries given by products of the original
matrix entries. A nonzero eigenvector v produces the nonzero
elementary tensor v⊗...⊗v with eigenvalue α^k.

The construction requires no diagonalizability, and the extension
degree e is implemented by replacing A with its matrix power A^e.
The change from the original Q_l vector space to C, and the
etale-cohomology Künneth equivalence, remain separate obligations.
-/

open scoped BigOperators Matrix
open Finset

namespace Deligne06

/-- k-fold tensor matrix in the standard elementary-tensor basis. -/
def tensorMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Matrix (Fin k → Fin n) (Fin k → Fin n) ℂ :=
  Matrix.of fun x y => ∏ j : Fin k, A (x j) (y j)

/-- An elementary pure tensor vector. -/
def tensorVector {n : ℕ}
    (v : Fin n → ℂ) (k : ℕ) :
    (Fin k → Fin n) → ℂ :=
  fun x => ∏ j : Fin k, v (x j)

/-- Matrix multiplication on the pure tensor separates by factor.
This identity holds even for operators with nontrivial Jordan blocks. -/
theorem tensorMatrix_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (k : ℕ)
    (x : Fin k → Fin n) :
    ((tensorMatrix A k) *ᵥ (tensorVector v k)) x =
      ∏ j : Fin k, (A *ᵥ v) (x j) := by
  classical
  change (∑ y : Fin k → Fin n,
    (∏ j : Fin k, A (x j) (y j)) *
      (∏ j : Fin k, v (y j))) =
    ∏ j : Fin k, ∑ z : Fin n, A (x j) z * v z
  calc
    (∑ y : Fin k → Fin n,
      (∏ j : Fin k, A (x j) (y j)) *
        (∏ j : Fin k, v (y j))) =
      ∑ y : Fin k → Fin n,
        ∏ j : Fin k, A (x j) (y j) * v (y j) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.prod_mul_distrib]
    _ = ∏ j : Fin k, ∑ z : Fin n, A (x j) z * v z :=
      (Fintype.prod_sum
        (fun j z => A (x j) z * v z)).symm

/-- The elementary tensor has eigenvalue α^k. -/
theorem tensor_eigenvector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (alpha : ℂ) (k : ℕ)
    (hv : A *ᵥ v = alpha • v) :
    (tensorMatrix A k) *ᵥ (tensorVector v k) =
      (alpha ^ k) • tensorVector v k := by
  funext x
  rw [tensorMatrix_mulVec]
  have hi : ∀ j : Fin k,
      (A *ᵥ v) (x j) = alpha * v (x j) := by
    intro j
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hv (x j)
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]
  simp [tensorVector, smul_eq_mul]

/-- If v has a nonzero coordinate, then its k-fold pure tensor
is a nonzero vector, including for k=0. -/
theorem tensorVector_ne_zero {n : ℕ}
    (v : Fin n → ℂ) (k : ℕ)
    (i : Fin n) (hvi : v i ≠ 0) :
    tensorVector v k ≠ 0 := by
  intro hz
  have hx := congrFun hz (fun _ : Fin k => i)
  have hpow : (v i) ^ k = 0 := by
    simpa [tensorVector] using hx
  exact (pow_ne_zero k hvi) hpow

/-- An actual nonzero eigenvector exhibits the tensor eigenvalue. -/
theorem tensor_eigenvalue_occurs {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (alpha : ℂ) (k : ℕ)
    (i : Fin n) (hvi : v i ≠ 0)
    (hv : A *ᵥ v = alpha • v) :
    ∃ w : (Fin k → Fin n) → ℂ,
      w ≠ 0 ∧ (tensorMatrix A k) *ᵥ w = (alpha ^ k) • w := by
  exact ⟨tensorVector v k, tensorVector_ne_zero v k i hvi,
    tensor_eigenvector A v alpha k hv⟩

/-- Matrix powers preserve eigenvectors and raise the eigenvalue. -/
theorem matrix_power_eigenvector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (alpha : ℂ)
    (hv : A *ᵥ v = alpha • v) (e : ℕ) :
    A ^ e *ᵥ v = (alpha ^ e) • v := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_smul, ih]
      simp [pow_succ, smul_smul, mul_comm]

/-- The exact eigenvalue α^(k*e) required by DEL-05 appears
in the k-fold tensor of the e-th Frobenius power. -/
theorem tensor_extension_eigenvalue_occurs {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (alpha : ℂ) (k e : ℕ)
    (i : Fin n) (hvi : v i ≠ 0)
    (hv : A *ᵥ v = alpha • v) :
    ∃ w : (Fin k → Fin n) → ℂ,
      w ≠ 0 ∧
        (tensorMatrix (A ^ e) k) *ᵥ w =
          (alpha ^ (k * e)) • w := by
  obtain ⟨w, hnonzero, heig⟩ :=
    tensor_eigenvalue_occurs (A ^ e) v (alpha ^ e) k i hvi
      (matrix_power_eigenvector A v alpha hv e)
  refine ⟨w, hnonzero, ?_⟩
  have hp : (alpha ^ e) ^ k = alpha ^ (k * e) := by
    rw [← pow_mul, Nat.mul_comm]
  simpa only [hp] using heig

#print axioms tensorMatrix_mulVec
#print axioms tensor_eigenvector
#print axioms tensorVector_ne_zero
#print axioms tensor_eigenvalue_occurs
#print axioms matrix_power_eigenvector
#print axioms tensor_extension_eigenvalue_occurs

end Deligne06
