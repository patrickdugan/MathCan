module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-!
# Ordinary bivariate degree and finite moment annihilation

The polynomial is Mathlib's actual `MvPolynomial (Fin 2) K`, with its
ordinary total degree. Its evaluation expands into its finitely supported
monomials. A finite weighted functional that vanishes on all bounded-degree
monomials therefore vanishes on every polynomial under the same bound.
-/

@[expose] public section

namespace TRR08Geometry

open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def bivariateEval (F : MvPolynomial (Fin 2) K) (x y : K) : K :=
  MvPolynomial.eval ![x, y] F

theorem bivariate_exponent_sum (e : Fin 2 →₀ ℕ) :
    (e.sum fun _ n => n) = e 0 + e 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]

theorem bivariate_support_totalDegree (F : MvPolynomial (Fin 2) K)
    {e : Fin 2 →₀ ℕ} (he : e ∈ F.support) :
    e 0 + e 1 ≤ F.totalDegree := by
  rw [← bivariate_exponent_sum]
  exact MvPolynomial.le_totalDegree he

theorem bivariate_support_weight_le (F : MvPolynomial (Fin 2) K)
    {d : ℕ} (hd : F.totalDegree ≤ d) {e : Fin 2 →₀ ℕ} (he : e ∈ F.support) :
    2 * e 0 + 3 * e 1 ≤ 3 * d := by
  have h := (bivariate_support_totalDegree F he).trans hd
  omega

theorem bivariateEval_eq_sum (F : MvPolynomial (Fin 2) K) (x y : K) :
    bivariateEval F x y =
      ∑ e ∈ F.support, F.coeff e * (x ^ e 0 * y ^ e 1) := by
  unfold bivariateEval
  rw [MvPolynomial.eval_eq']
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Actual ordinary polynomial evaluation is annihilated by its monomial moments. -/
theorem sum_bivariateEval_eq_zero_of_moments {ι : Type*} [Fintype ι]
    (w x y : ι → K) (F : MvPolynomial (Fin 2) K) {d : ℕ}
    (hd : F.totalDegree ≤ d)
    (hmom : ∀ a b : ℕ, a + b ≤ d → ∑ Q : ι, w Q * x Q ^ a * y Q ^ b = 0) :
    (∑ Q : ι, w Q * bivariateEval F (x Q) (y Q)) = 0 := by
  classical
  simp_rw [bivariateEval_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  have hz := hmom (e 0) (e 1) ((bivariate_support_totalDegree F he).trans hd)
  calc
    (∑ Q : ι, w Q * (F.coeff e * (x Q ^ e 0 * y Q ^ e 1))) =
        F.coeff e * ∑ Q : ι, w Q * x Q ^ e 0 * y Q ^ e 1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      ring
    _ = 0 := by rw [hz, mul_zero]

/-- Pole-weight moments imply ordinary-degree annihilation using weights two and three. -/
theorem sum_bivariateEval_eq_zero_of_weighted_moments {ι : Type*} [Fintype ι]
    (w x y : ι → K) (F : MvPolynomial (Fin 2) K) {d B : ℕ}
    (hd : F.totalDegree ≤ d) (hB : 3 * d ≤ B)
    (hmom : ∀ a b : ℕ, 2 * a + 3 * b ≤ B →
      ∑ Q : ι, w Q * x Q ^ a * y Q ^ b = 0) :
    (∑ Q : ι, w Q * bivariateEval F (x Q) (y Q)) = 0 := by
  apply sum_bivariateEval_eq_zero_of_moments w x y F hd
  intro a b hab
  apply hmom a b
  omega

end TRR08Geometry

#print axioms TRR08Geometry.bivariate_exponent_sum
#print axioms TRR08Geometry.bivariate_support_totalDegree
#print axioms TRR08Geometry.bivariate_support_weight_le
#print axioms TRR08Geometry.bivariateEval_eq_sum
#print axioms TRR08Geometry.sum_bivariateEval_eq_zero_of_moments
#print axioms TRR08Geometry.sum_bivariateEval_eq_zero_of_weighted_moments
