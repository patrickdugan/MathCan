import Deligne04.GysinTrace
import Mathlib.Tactic

/-!
# DEL-06: Gysin kernel and high-degree trace identities for every n

Proposition 4 needs Frobenius powers, not just first-power traces.
These theorems prove the complete finite-dimensional block-matrix
statement under explicit Frobenius-compatible Gysin bases. The input
is the algebraic shadow of the geometric restriction/Gysin maps.
-/

open scoped BigOperators Matrix
open Finset

namespace Deligne06

/-- Every power of a kernel-adapted boundary Frobenius remains
upper triangular, with the expected powers on its diagonal. -/
theorem boundary_pow_blocks {a b : ℕ}
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ)
    (n : ℕ) :
    ∃ mixN : Matrix (Fin a) (Fin b) ℂ,
      (boundaryFrob K Q mix) ^ n =
        boundaryFrob (K ^ n) (Q ^ n) mixN := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      simp [boundaryFrob]
  | succ n ih =>
      obtain ⟨mixN, hmixN⟩ := ih
      refine ⟨K ^ n * mix + mixN * Q, ?_⟩
      rw [pow_succ, hmixN]
      simp [boundaryFrob, Matrix.fromBlocks_multiply, pow_succ]

/-- The boundary kernel/quotient trace decomposition works for every
Frobenius power. The off-diagonal extension can be arbitrary. -/
theorem boundary_trace_all_powers {a b : ℕ}
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ)
    (n : ℕ) :
    Matrix.trace ((boundaryFrob K Q mix) ^ n) =
      Matrix.trace (K ^ n) + Matrix.trace (Q ^ n) := by
  obtain ⟨mixN, h⟩ := boundary_pow_blocks K Q mix n
  rw [h]
  exact boundary_trace (K ^ n) (Q ^ n) mixN

/-- A conjugated Frobenius has conjugate powers as long as its
change-of-basis matrices are mutual inverses. -/
theorem conjugate_pow {t : ℕ}
    (X P Pinv : Matrix (Fin t) (Fin t) ℂ)
    (hleft : Pinv * P = 1)
    (hright : P * Pinv = 1)
    (n : ℕ) :
    (P * X * Pinv) ^ n = P * X ^ n * Pinv := by
  induction n with
  | zero =>
      simp [hright]
  | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      calc
        (P * X ^ n * Pinv) * (P * X * Pinv) =
            P * X ^ n * (Pinv * P) * X * Pinv := by
          simp only [mul_assoc]
        _ = P * (X ^ n * X) * Pinv := by
          rw [hleft]
          simp only [mul_one, mul_assoc]

/-- Frobenius-compatible isomorphisms preserve the traces of all
powers; here the isomorphism is supplied by invertible matrices. -/
theorem trace_conjugate_all_powers {t : ℕ}
    (X P Pinv : Matrix (Fin t) (Fin t) ℂ)
    (hleft : Pinv * P = 1)
    (hright : P * Pinv = 1)
    (n : ℕ) :
    Matrix.trace ((P * X * Pinv) ^ n) =
      Matrix.trace (X ^ n) := by
  rw [conjugate_pow X P Pinv hleft hright n]
  exact trace_conjugate (X ^ n) P Pinv hleft

/-- The signed remainder's complete Frobenius-power expansion.
The base field's Tate twist has been incorporated into the
Y-side Frobenius operators before this algebraic calculation. -/
def signedPowerRemainder {a b c h t : ℕ}
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin c) (Fin c) ℂ)
    (Yhigh Xhigh : Fin h → Matrix (Fin t) (Fin t) ℂ)
    (n : ℕ) : ℂ :=
  Matrix.trace ((boundaryFrob K Q mix) ^ n) -
    Matrix.trace (Q ^ n) +
      Matrix.trace (L ^ n) +
      ∑ i : Fin h, (-1 : ℂ) ^ (i.val + 1) *
        (Matrix.trace ((Yhigh i) ^ n) -
          Matrix.trace ((Xhigh i) ^ n))

/-- The all-powers Gysin cancellation. This is the exact algebraic
sign lemma needed to supply DEL-05 with a genuine kernel trace. -/
theorem gysin_signed_all_powers
    {a b c h t : ℕ}
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin c) (Fin c) ℂ)
    (Yhigh Xhigh P Pinv : Fin h →
      Matrix (Fin t) (Fin t) ℂ)
    (hinvL : ∀ i, Pinv i * P i = 1)
    (hinvR : ∀ i, P i * Pinv i = 1)
    (hconj : ∀ i, Yhigh i = P i * Xhigh i * Pinv i)
    (n : ℕ) :
    signedPowerRemainder K Q mix L Yhigh Xhigh n =
      Matrix.trace (K ^ n) + Matrix.trace (L ^ n) := by
  have hpair : ∀ i, Matrix.trace ((Yhigh i) ^ n) =
      Matrix.trace ((Xhigh i) ^ n) := by
    intro i
    rw [hconj i]
    exact trace_conjugate_all_powers
      (Xhigh i) (P i) (Pinv i) (hinvL i) (hinvR i) n
  simp [signedPowerRemainder, boundary_trace_all_powers, hpair]
  ring

/-- The Proposition 4 point-count identity follows for every n
from a separately supplied *geometric* trace-formula equality. -/
theorem proposition4_all_positive_powers
    {a b c h t : ℕ} (D : ℕ) (R : ℕ → ℂ)
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin c) (Fin c) ℂ)
    (Yhigh Xhigh P Pinv : Fin h →
      Matrix (Fin t) (Fin t) ℂ)
    (hinvL : ∀ i, Pinv i * P i = 1)
    (hinvR : ∀ i, P i * Pinv i = 1)
    (hconj : ∀ i, Yhigh i = P i * Xhigh i * Pinv i)
    (htrace : ∀ n, 0 < n →
      (-1 : ℂ) ^ (D - 1) * R n =
        signedPowerRemainder K Q mix L Yhigh Xhigh n) :
    ∀ n, 0 < n →
      (-1 : ℂ) ^ (D - 1) * R n =
        Matrix.trace (K ^ n) + Matrix.trace (L ^ n) := by
  intro n hn
  rw [htrace n hn]
  exact gysin_signed_all_powers
    K Q mix L Yhigh Xhigh P Pinv hinvL hinvR hconj n

#print axioms boundary_pow_blocks
#print axioms boundary_trace_all_powers
#print axioms conjugate_pow
#print axioms trace_conjugate_all_powers
#print axioms gysin_signed_all_powers
#print axioms proposition4_all_positive_powers

end Deligne06
