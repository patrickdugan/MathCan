module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-!
# Ordinary coordinate-pair degree for an actual four-variable polynomial

The support condition bounds the sum of exponents in each coordinate pair.
Expanding evaluation into actual monomials transfers any finite moment
annihilator to every polynomial satisfying that block bound.
-/

@[expose] public section

namespace TRR08Geometry

open scoped BigOperators

variable {K : Type*} [CommSemiring K]

/-- Ordinary total degree at most `d` in each of the two coordinate pairs. -/
def BlockDegreeLE (d : ℕ) (D : MvPolynomial (Fin 4) K) : Prop :=
  ∀ e ∈ D.support, e 0 + e 1 ≤ d ∧ e 2 + e 3 ≤ d

/-- Evaluation of an actual polynomial at the two coordinate pairs. -/
noncomputable def blockEval (D : MvPolynomial (Fin 4) K)
    (x₁ y₁ x₂ y₂ : K) : K :=
  MvPolynomial.eval ![x₁, y₁, x₂, y₂] D

theorem blockEval_eq_sum (D : MvPolynomial (Fin 4) K) (x₁ y₁ x₂ y₂ : K) :
    blockEval D x₁ y₁ x₂ y₂ =
      ∑ e ∈ D.support, D.coeff e * x₁ ^ e 0 * y₁ ^ e 1 * x₂ ^ e 2 * y₂ ^ e 3 := by
  simp [blockEval, MvPolynomial.eval_eq', Fin.prod_univ_four, mul_assoc]

/-- Every bounded block polynomial is annihilated in its second coordinate
pair when all ordinary-degree moments through the same bound vanish. -/
theorem sum_blockEval_right_eq_zero_of_moments {ι : Type*} [Fintype ι]
    (w x y : ι → K) (d : ℕ)
    (hmom : ∀ a b : ℕ, a + b ≤ d → ∑ Q : ι, w Q * x Q ^ a * y Q ^ b = 0)
    (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D) (x₁ y₁ : K) :
    (∑ Q : ι, w Q * blockEval D x₁ y₁ (x Q) (y Q)) = 0 := by
  classical
  simp_rw [blockEval_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  calc
    (∑ Q : ι, w Q *
        (D.coeff e * x₁ ^ e 0 * y₁ ^ e 1 * x Q ^ e 2 * y Q ^ e 3)) =
        (D.coeff e * x₁ ^ e 0 * y₁ ^ e 1) *
          (∑ Q : ι, w Q * x Q ^ e 2 * y Q ^ e 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      ring
    _ = 0 := by rw [hmom (e 2) (e 3) (hD e he).2, mul_zero]

theorem sum_blockEval_left_eq_zero_of_moments {ι : Type*} [Fintype ι]
    (w x y : ι → K) (d : ℕ)
    (hmom : ∀ a b : ℕ, a + b ≤ d → ∑ P : ι, w P * x P ^ a * y P ^ b = 0)
    (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D) (x₂ y₂ : K) :
    (∑ P : ι, w P * blockEval D (x P) (y P) x₂ y₂) = 0 := by
  classical
  simp_rw [blockEval_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  calc
    (∑ P : ι, w P *
        (D.coeff e * x P ^ e 0 * y P ^ e 1 * x₂ ^ e 2 * y₂ ^ e 3)) =
        (D.coeff e * x₂ ^ e 2 * y₂ ^ e 3) *
          (∑ P : ι, w P * x P ^ e 0 * y P ^ e 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      ring
    _ = 0 := by rw [hmom (e 0) (e 1) (hD e he).1, mul_zero]

end TRR08Geometry

#print axioms TRR08Geometry.blockEval_eq_sum
#print axioms TRR08Geometry.sum_blockEval_right_eq_zero_of_moments
#print axioms TRR08Geometry.sum_blockEval_left_eq_zero_of_moments
