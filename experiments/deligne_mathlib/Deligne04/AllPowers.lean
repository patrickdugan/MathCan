import Deligne04.Isolation
import Deligne04.ScalarGrowth
import Mathlib.Tactic

/-!
DEL-04: the fixed-spectrum all-powers theorem.

This is the complete analytic/algebraic power-sum bound for a finite
complex spectrum with pairwise distinct eigenvalues and nonzero
aggregated multiplicities, using Vandermonde isolation rather than
complex generating functions. The geometric trace realization,
tensor-power quantifiers and k-th root limit remain outside.
-/

open scoped BigOperators Matrix
open Finset

namespace Deligne04

/-- If a finite sequence of complex weighted power sums is bounded
uniformly in every nonnegative power by C B^n with B>0, each
nonzero-multiplicity eigenvalue has norm at most B. -/
theorem finite_spectral_power_bound {s : ℕ}
    (lam weights : Fin s → ℂ)
    (hinj : Function.Injective lam)
    (hw : ∀ i, weights i ≠ 0)
    {B C : ℝ} (hB : 0 < B)
    (htrace : ∀ n : ℕ,
      ‖powerTrace lam weights n‖ ≤ C * B ^ n) :
    ∀ i : Fin s, ‖lam i‖ ≤ B := by
  intro i
  obtain ⟨coeff, hcoeff⟩ :=
    exists_trace_window_extractor lam weights hinj i
  have hwindow : ∀ n : ℕ,
      ‖weights i * lam i ^ n‖ ≤
        (C * (∑ r : Fin s, ‖coeff r‖ * B ^ r.val)) * B ^ n := by
    intro n
    calc
      ‖weights i * lam i ^ n‖ =
          ‖∑ r : Fin s, coeff r * powerTrace lam weights (n + r.val)‖ := by
            rw [hcoeff n]
      _ ≤ ∑ r : Fin s,
          ‖coeff r * powerTrace lam weights (n + r.val)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ r : Fin s,
          ‖coeff r‖ * (C * B ^ (n + r.val)) := by
            apply Finset.sum_le_sum
            intro r _
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left
              (htrace (n + r.val)) (norm_nonneg _)
      _ = (C * (∑ r : Fin s, ‖coeff r‖ * B ^ r.val)) * B ^ n := by
            calc
              (∑ r : Fin s, ‖coeff r‖ * (C * B ^ (n + r.val))) =
                  ∑ r : Fin s, (C * B ^ n) * (‖coeff r‖ * B ^ r.val) := by
                    apply Finset.sum_congr rfl
                    intro r _
                    rw [pow_add]
                    ring
              _ = (C * B ^ n) *
                  (∑ r : Fin s, ‖coeff r‖ * B ^ r.val) := by
                    rw [Finset.mul_sum]
              _ = (C * (∑ r : Fin s, ‖coeff r‖ * B ^ r.val)) * B ^ n := by
                    ring
  exact complex_weighted_power_growth_le (lam i) (weights i)
    hB (hw i) hwindow

/-- The form used in Lemma 2: the trace bound is only assumed
for strictly positive powers. Enlarge its constant to control n=0. -/
theorem finite_spectral_power_bound_pos {s : ℕ}
    (lam weights : Fin s → ℂ)
    (hinj : Function.Injective lam)
    (hw : ∀ i, weights i ≠ 0)
    {B C : ℝ} (hB : 0 < B)
    (htrace : ∀ n : ℕ, 0 < n →
      ‖powerTrace lam weights n‖ ≤ C * B ^ n) :
    ∀ i : Fin s, ‖lam i‖ ≤ B := by
  let C' : ℝ := max C ‖powerTrace lam weights 0‖
  have hfull : ∀ n : ℕ,
      ‖powerTrace lam weights n‖ ≤ C' * B ^ n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simpa [C'] using (le_max_right C ‖powerTrace lam weights 0‖)
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      apply (htrace n hnpos).trans
      dsimp [C']
      exact mul_le_mul_of_nonneg_right
        (le_max_left C ‖powerTrace lam weights 0‖)
        (pow_nonneg (le_of_lt hB) n)
  exact finite_spectral_power_bound lam weights hinj hw hB hfull

#print axioms finite_spectral_power_bound_pos

#print axioms finite_spectral_power_bound

end Deligne04
