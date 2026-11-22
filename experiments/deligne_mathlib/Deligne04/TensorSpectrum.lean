import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# DEL-06: finite tensor spectra and their Frobenius trace

The complex tensor spectrum is indexed by all functions Fin k → Fin n,
so repeated eigenvalues are retained with their genuine multiplicity.
These identities hold for diagonal Frobenius modules. Moving from an
arbitrary (possibly nonsemisimple) étale-cohomology operator to that
finite spectral list is a separately identified geometric/linear-
algebraic obligation.
-/

open scoped BigOperators Matrix
open Finset

namespace Deligne06

/-- The spectral value attached to one elementary k-fold tensor. -/
def tensorEigenvalue {n : ℕ} (lam : Fin n → ℂ)
    (k : ℕ) (indices : Fin k → Fin n) : ℂ :=
  ∏ t : Fin k, lam (indices t)

/-- Repeating an eigenvalue k times produces its k-th power. -/
theorem tensor_eigenvalue_repeated {n : ℕ} (lam : Fin n → ℂ)
    (k : ℕ) (i : Fin n) :
    tensorEigenvalue lam k (fun _ => i) = lam i ^ k := by
  simp [tensorEigenvalue]

/-- The trace of the diagonal k-fold tensor operator is the k-th
power of the trace on its base space. This includes k=0. -/
theorem tensor_trace {n : ℕ} (lam : Fin n → ℂ) (k : ℕ) :
    (∑ x : Fin k → Fin n, tensorEigenvalue lam k x) =
      (∑ i : Fin n, lam i) ^ k := by
  simpa only [tensorEigenvalue] using (Fintype.sum_pow lam k).symm

/-- Every positive power of a diagonal tensor operator has the
same trace as the tensor product of that power on the base space. -/
theorem tensor_trace_power {n : ℕ} (lam : Fin n → ℂ)
    (k e : ℕ) :
    (∑ x : Fin k → Fin n, (tensorEigenvalue lam k x) ^ e) =
      (∑ i : Fin n, (lam i) ^ e) ^ k := by
  simp only [tensorEigenvalue, Finset.prod_pow]
  exact (Fintype.sum_pow (fun i : Fin n => (lam i) ^ e) k).symm

/-- The diagonal matrix realizing this finite tensor spectrum. -/
def diagonalTensorFrob {n : ℕ} (lam : Fin n → ℂ) (k : ℕ) :
    Matrix (Fin k → Fin n) (Fin k → Fin n) ℂ :=
  Matrix.diagonal (tensorEigenvalue lam k)

/-- Its matrix trace is exactly the tensor power trace. -/
theorem diagonal_tensor_trace {n : ℕ} (lam : Fin n → ℂ) (k : ℕ) :
    Matrix.trace (diagonalTensorFrob lam k) =
      (∑ i : Fin n, lam i) ^ k := by
  simpa only [diagonalTensorFrob, Matrix.trace_diagonal]
    using tensor_trace lam k

/-- The distinguished tensor eigenvalue exists as an actual index
of the diagonal k-fold tensor spectrum. -/
theorem diagonal_tensor_eigenvalue_occurs {n : ℕ}
    (lam : Fin n → ℂ) (k : ℕ) (i : Fin n) :
    ∃ x : Fin k → Fin n,
      diagonalTensorFrob lam k x x = (lam i) ^ k := by
  refine ⟨fun _ => i, ?_⟩
  simpa [diagonalTensorFrob, Matrix.diagonal_apply_eq]
    using tensor_eigenvalue_repeated lam k i

#print axioms tensor_eigenvalue_repeated
#print axioms tensor_trace
#print axioms tensor_trace_power
#print axioms diagonal_tensor_trace
#print axioms diagonal_tensor_eigenvalue_occurs

end Deligne06
