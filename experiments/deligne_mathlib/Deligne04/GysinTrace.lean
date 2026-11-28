import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# DEL-06: Frobenius-equivariant Gysin boundary sign

This finite-dimensional matrix model isolates the precise cancellation
in Proposition 4 of hexagon:2611.00789v1. An equivariant surjection
admits a block-upper-triangular matrix in a basis adapted to its
kernel. Higher-degree Gysin isomorphisms are represented by invertible
change-of-basis matrices. The étale cohomology, existence of those
Gysin maps and identification of the Frobenius modules are separate
geometric premises.
-/

open scoped BigOperators Matrix
open Finset

namespace Deligne06

/-- Algebraic Frobenius action on a Gysin domain, in a kernel-adapted
basis: K is stable, Q is the quotient, and mix is arbitrary. -/
def boundaryFrob {a b : ℕ}
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ) :
    Matrix (Sum (Fin a) (Fin b)) (Sum (Fin a) (Fin b)) ℂ :=
  Matrix.fromBlocks K mix 0 Q

/-- The boundary Frobenius trace is a *sum* of genuine kernel and
quotient traces, including in the presence of extension data mix. -/
theorem boundary_trace {a b : ℕ}
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ) :
    Matrix.trace (boundaryFrob K Q mix) =
      Matrix.trace K + Matrix.trace Q := by
  simp only [boundaryFrob, Matrix.trace, Fintype.sum_sum_type,
    Matrix.diag_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂]

/-- Frobenius conjugacy preserves trace, the linear-algebraic
consequence of a Frobenius-compatible Gysin isomorphism. -/
theorem trace_conjugate {h : ℕ}
    (X P Pinv : Matrix (Fin h) (Fin h) ℂ)
    (hleft : Pinv * P = 1) :
    Matrix.trace (P * X * Pinv) = Matrix.trace X := by
  calc
    Matrix.trace (P * X * Pinv) =
        Matrix.trace (Pinv * P * X) :=
      Matrix.trace_mul_cycle P X Pinv
    _ = Matrix.trace X := by rw [hleft, one_mul]

/-- The (-1)-Tate twist multiplies a Frobenius trace by the
size r of the base field, in the designated complex embedding. -/
theorem tate_minus_one_trace {h : ℕ} (r : ℂ)
    (X : Matrix (Fin h) (Fin h) ℂ) :
    Matrix.trace (r • X) = r * Matrix.trace X := by
  simp [smul_eq_mul]

/-- The already-sign-adjusted alternating remainder. The higher
degrees appear in paired positions with opposite signs. -/
def signedRemainder {a b c h : ℕ}
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin c) (Fin c) ℂ)
    (Yhigh Xhigh : Fin h → ℂ) : ℂ :=
  Matrix.trace (boundaryFrob K Q mix) -
    Matrix.trace Q + Matrix.trace L +
      ∑ i : Fin h, (-1 : ℂ) ^ (i.val + 1) * (Yhigh i - Xhigh i)

/-- Once each higher-degree trace pair agrees, Proposition 4's
surviving terms have the same sign. -/
theorem gysin_signed_remainder {a b c h : ℕ}
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin c) (Fin c) ℂ)
    (Yhigh Xhigh : Fin h → ℂ)
    (hpaired : ∀ i, Yhigh i = Xhigh i) :
    signedRemainder K Q mix L Yhigh Xhigh =
      Matrix.trace K + Matrix.trace L := by
  simp [signedRemainder, boundary_trace, hpaired]

/-- The pairing can be proved from explicit Frobenius conjugacies,
rather than assuming equality of high-degree traces. -/
theorem gysin_from_equivariant_isomorphisms
    {a b c h t : ℕ}
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin c) (Fin c) ℂ)
    (Yhigh Xhigh P Pinv : Fin h →
      Matrix (Fin t) (Fin t) ℂ)
    (hinv : ∀ i, Pinv i * P i = 1)
    (hconj : ∀ i, Yhigh i = P i * Xhigh i * Pinv i) :
    signedRemainder K Q mix L
      (fun i => Matrix.trace (Yhigh i))
      (fun i => Matrix.trace (Xhigh i)) =
      Matrix.trace K + Matrix.trace L := by
  apply gysin_signed_remainder
  intro i
  rw [hconj i]
  exact trace_conjugate (Xhigh i) (P i) (Pinv i) (hinv i)

/-- The sign of the *original* point-count remainder is explicitly
tracked. The trace formula still appears as its geometric hypothesis. -/
theorem proposition4_signed_point_count
    {a b c h : ℕ} (D : ℕ) (R : ℂ)
    (K : Matrix (Fin a) (Fin a) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ)
    (mix : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin c) (Fin c) ℂ)
    (Yhigh Xhigh : Fin h → ℂ)
    (hpaired : ∀ i, Yhigh i = Xhigh i)
    (htrace : (-1 : ℂ) ^ (D - 1) * R =
      signedRemainder K Q mix L Yhigh Xhigh) :
    (-1 : ℂ) ^ (D - 1) * R =
      Matrix.trace K + Matrix.trace L := by
  rw [htrace]
  exact gysin_signed_remainder K Q mix L Yhigh Xhigh hpaired

#print axioms boundary_trace
#print axioms trace_conjugate
#print axioms tate_minus_one_trace
#print axioms gysin_signed_remainder
#print axioms gysin_from_equivariant_isomorphisms
#print axioms proposition4_signed_point_count

end Deligne06
