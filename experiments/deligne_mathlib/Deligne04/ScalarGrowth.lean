import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic

/-!
DEL-04: scalar growth of powers, the Archimedean part of the
all-powers spectral estimate. This is independent of eigenvalue
multiplicities or the geometry used to construct the trace bound.
-/

namespace Deligne04

/-- A geometric progression with a uniform relative exponential
bound cannot have a base larger than the comparison base. -/
theorem real_growth_le {a b K : ℝ} (hb : 0 < b)
    (h : ∀ n : ℕ, a ^ n ≤ K * b ^ n) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hr : (1 : ℝ) < a / b := (one_lt_div hb).mpr hba
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt K hr
  have hbn : 0 < b ^ n := pow_pos hb n
  have hdiv : a ^ n / b ^ n ≤ K :=
    (div_le_iff₀ hbn).mpr (h n)
  have hp : (a / b) ^ n ≤ K := by
    simpa only [div_pow] using hdiv
  exact (not_lt_of_ge hp) hn

/-- The complex absolute-value version. -/
theorem complex_power_growth_le (z : ℂ) {B K : ℝ} (hB : 0 < B)
    (h : ∀ n : ℕ, ‖z ^ n‖ ≤ K * B ^ n) : ‖z‖ ≤ B := by
  apply real_growth_le hB
  intro n
  simpa only [norm_pow] using h n

/-- The nonzero isolating coefficient in the finite spectral
extraction cannot alter the asymptotic exponential rate. -/
theorem complex_weighted_power_growth_le (z w : ℂ) {B K : ℝ}
    (hB : 0 < B) (hw : w ≠ 0)
    (h : ∀ n : ℕ, ‖w * z ^ n‖ ≤ K * B ^ n) : ‖z‖ ≤ B := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  apply real_growth_le hB
  intro n
  have hi : ‖w‖ * ‖z‖ ^ n ≤ K * B ^ n := by
    simpa only [norm_mul, norm_pow] using h n
  have hi' : ‖z‖ ^ n * ‖w‖ ≤ K * B ^ n := by
    simpa only [mul_comm] using hi
  have hdiv : ‖z‖ ^ n ≤ (K * B ^ n) / ‖w‖ :=
    (le_div_iff₀ hwpos).mpr hi'
  calc
    ‖z‖ ^ n ≤ (K * B ^ n) / ‖w‖ := hdiv
    _ = (K / ‖w‖) * B ^ n := by ring

#print axioms real_growth_le
#print axioms complex_power_growth_le
#print axioms complex_weighted_power_growth_le

end Deligne04
