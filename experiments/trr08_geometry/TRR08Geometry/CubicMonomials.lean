module

public import TRR08Geometry.MarkedPoints
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Ordinary monomials restricted to a short Weierstrass equation

The even and odd powers of the y-coordinate reduce to explicit univariate
polynomials. Their degree bounds will supply the finite residue annihilation
argument for actual coordinate polynomials.
-/

@[expose] public section

namespace TRR08Geometry

open Polynomial WeierstrassCurve

variable {K : Type*} [Field K]

noncomputable def shortCubic (A B : K) : K[X] := X^3 + C A * X + C B

noncomputable def cubicMonomial (A B : K) (a k : ℕ) : K[X] :=
  X^a * shortCubic A B ^ k

theorem shortCubic_natDegree_le (A B : K) : (shortCubic A B).natDegree ≤ 3 := by
  unfold shortCubic
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · apply natDegree_mul_le.trans
      simp
  · simp

theorem cubicMonomial_natDegree_le (A B : K) (a k : ℕ) :
    (cubicMonomial A B a k).natDegree ≤ a + 3*k := by
  unfold cubicMonomial
  apply natDegree_mul_le.trans
  apply Nat.add_le_add
  · simp
  · simpa [Nat.mul_comm] using natDegree_pow_le_of_le k (shortCubic_natDegree_le A B)

@[simp] theorem shortCubic_eval (A B x : K) :
    (shortCubic A B).eval x = x^3 + A*x + B := by
  simp [shortCubic]

@[simp] theorem cubicMonomial_eval (A B x : K) (a k : ℕ) :
    (cubicMonomial A B a k).eval x = x^a * (x^3 + A*x + B)^k := by
  simp [cubicMonomial]

variable {W : Affine K} [W.IsShortNF]

theorem even_monomial_on_curve {P : W.Point} (hP : P ≠ 0) (a k : ℕ) :
    affineX P ^ a * affineY P ^ (2*k) =
      (cubicMonomial W.a₄ W.a₆ a k).eval (affineX P) := by
  rw [cubicMonomial_eval, ← short_curve_equation hP, pow_mul]

theorem odd_monomial_on_curve {P : W.Point} (hP : P ≠ 0) (a k : ℕ) :
    affineX P ^ a * affineY P ^ (2*k+1) =
      affineY P * (cubicMonomial W.a₄ W.a₆ a k).eval (affineX P) := by
  rw [pow_succ, ← mul_assoc, even_monomial_on_curve hP]
  ring

end TRR08Geometry

#print axioms TRR08Geometry.shortCubic_natDegree_le
#print axioms TRR08Geometry.cubicMonomial_natDegree_le
#print axioms TRR08Geometry.shortCubic_eval
#print axioms TRR08Geometry.cubicMonomial_eval
#print axioms TRR08Geometry.even_monomial_on_curve
#print axioms TRR08Geometry.odd_monomial_on_curve
