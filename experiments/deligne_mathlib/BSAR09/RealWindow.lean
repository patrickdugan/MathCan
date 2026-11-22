import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# BSAR-09R: real finite-product bound under a dimensionless window budget

This is isolated under MathCan's pinned Mathlib 4.35.0 subproject.
The main MathCan Init-only project remains unchanged.

The finite window inequalities are conditional and source-aligned with
BSA-R Step7. The real product estimate uses Mathlib's existing
Real.prod_one_add_le_exp_sum theorem.

This file assumes a global bound on the sum of I_m/M. It does not
derive that budget from any Navier-Stokes solution or direction field.
-/

namespace BSAR09Real

open Finset

/-- Exact real finite-product inequality, without finite-window counts. -/
theorem ratio_product_le_exp_sum
    {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∏ i ∈ s, (1 + 2 * a i)) ≤
      Real.exp (2 * ∑ i ∈ s, a i) := by
  have hnonneg (i : ι) : 0 ≤ (2 : ℝ) * a i :=
    mul_nonneg (by norm_num) (ha i)
  calc
    (∏ i ∈ s, (1 + 2 * a i)) ≤
        Real.exp (∑ i ∈ s, 2 * a i) :=
      Real.prod_one_add_le_exp_sum s hnonneg
    _ = Real.exp (2 * ∑ i ∈ s, a i) := by
      simp only [Finset.mul_sum]

/-- If the sum of dimensionless costs stays below B, the product
is bounded by exp(2 B) independently of the number of windows. -/
theorem ratio_product_le_exp_budget
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hbudget : (∑ i ∈ s, a i) ≤ B) :
    (∏ i ∈ s, (1 + 2 * a i)) ≤ Real.exp (2 * B) := by
  have hmul : 2 * (∑ i ∈ s, a i) ≤ 2 * B :=
    mul_le_mul_of_nonneg_left hbudget (by norm_num)
  exact (ratio_product_le_exp_sum s a ha).trans
    (Real.exp_monotone hmul)

/-- The original source ODE and the half-budget condition imply
the local factor 1 + 2*(I/M) for real-valued states. -/
theorem source_window_real_factor
    {M I dprev dnext : ℝ}
    (hM : 0 < M) (hI : 0 ≤ I) (hnn : 0 ≤ dnext)
    (hode : M * (dnext - dprev) ≤ I * dnext)
    (hhalf : 2 * I ≤ M) :
    dnext ≤ (1 + 2 * (I / M)) * dprev := by
  have h2ode : (2 : ℝ) * (M * (dnext - dprev)) ≤ 2 * (I * dnext) :=
    mul_le_mul_of_nonneg_left hode (by norm_num)
  have hhalfMul : (2 * I) * dnext ≤ M * dnext :=
    mul_le_mul_of_nonneg_right hhalf hnn
  have hdouble : dnext ≤ 2 * dprev := by
    by_contra h
    have hg : 0 < dnext - 2 * dprev := by linarith
    have hp : 0 < M * (dnext - 2 * dprev) := mul_pos hM hg
    nlinarith [h2ode, hhalfMul]
  have hupper : I * dnext ≤ I * (2 * dprev) :=
    mul_le_mul_of_nonneg_left hdouble hI
  have hcross : M * dnext ≤ (M + 2 * I) * dprev := by
    nlinarith [hode, hupper]
  have hne : M ≠ 0 := ne_of_gt hM
  have hrw : (M + 2 * I) * dprev =
      M * ((1 + 2 * (I / M)) * dprev) := by
    field_simp [hne]
    ring
  rw [hrw] at hcross
  exact (mul_le_mul_left hM).mp hcross

/-- Iteration of the source-aligned real window rule yields the
finite product bound for each K. The nonnegative D assumption
is explicit even though the core cross-multiplication may need less. -/
theorem source_chain_product
    (M : ℝ) (I D : ℕ → ℝ) (K : ℕ)
    (hM : 0 < M)
    (hI : ∀ n, 0 ≤ I n)
    (hD : ∀ n, 0 ≤ D n)
    (hhalf : ∀ n, 2 * I n ≤ M)
    (hode : ∀ n, M * (D (n + 1) - D n) ≤ I n * D (n + 1)) :
    D K ≤ D 0 * ∏ n ∈ Finset.range K, (1 + 2 * (I n / M)) := by
  induction K with
  | zero =>
      simp
  | succ k ih =>
      have hlocal : D (k + 1) ≤ (1 + 2 * (I k / M)) * D k :=
        source_window_real_factor hM (hI k) (hD (k + 1))
          (hode k) (hhalf k)
      have hratio : 0 ≤ I k / M := div_nonneg (hI k) (le_of_lt hM)
      have hfac : 0 ≤ (1 + 2 * (I k / M)) := by positivity
      calc
        D (k + 1) ≤ (1 + 2 * (I k / M)) * D k := hlocal
        _ ≤ (1 + 2 * (I k / M)) *
            (D 0 * ∏ n ∈ Finset.range k, (1 + 2 * (I n / M))) :=
          mul_le_mul_of_nonneg_left ih hfac
        _ = D 0 * ∏ n ∈ Finset.range (k + 1), (1 + 2 * (I n / M)) := by
          rw [Finset.prod_range_succ]
          ring

/-- Fully real, K-independent bound under an independently supplied
dimensionless cost sum bound, with all local ODE assumptions explicit.
The PDE-to-window construction and global bound on B remain open. -/
theorem uniform_real_endpoint_bound
    (M : ℝ) (I D : ℕ → ℝ) (K : ℕ) (B : ℝ)
    (hM : 0 < M)
    (hI : ∀ n, 0 ≤ I n)
    (hD : ∀ n, 0 ≤ D n)
    (hhalf : ∀ n, 2 * I n ≤ M)
    (hode : ∀ n, M * (D (n + 1) - D n) ≤ I n * D (n + 1))
    (hbudget : (∑ n ∈ Finset.range K, I n / M) ≤ B) :
    D K ≤ D 0 * Real.exp (2 * B) := by
  have ha (i : ℕ) : 0 ≤ I i / M :=
    div_nonneg (hI i) (le_of_lt hM)
  have hproduct :=
    source_chain_product M I D K hM hI hD hhalf hode
  have hbudget_prod :=
    ratio_product_le_exp_budget (Finset.range K) (fun i => I i / M) B
      ha hbudget
  exact hproduct.trans (mul_le_mul_of_nonneg_left hbudget_prod (hD 0))

end BSAR09Real

#print axioms BSAR09Real.ratio_product_le_exp_sum
#print axioms BSAR09Real.ratio_product_le_exp_budget
#print axioms BSAR09Real.source_window_real_factor
#print axioms BSAR09Real.source_chain_product
#print axioms BSAR09Real.uniform_real_endpoint_bound
