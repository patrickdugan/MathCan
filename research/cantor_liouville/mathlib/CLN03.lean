import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate
open Finset

namespace CLN03

/-- Prefix conditional probabilities may be nonuniform or dependent.
For each fixed tail, a pointwise max-mass bound suffices. -/
theorem weighted_prefix_bound {A : Type*} [Fintype A]
    (mass E : A → ℝ) (α : ℝ)
    (hmass : ∀ a, mass a ≤ α) (hE : ∀ a, 0 ≤ E a) :
    (∑ a, mass a * E a) ≤ α * ∑ a, E a := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_right (hmass a) (hE a)

/-- A fiber of reduction modulo P among the first N integers
contains at most floor(N/P)+1 indices, including P=0 as a
harmless arithmetic convention. -/
theorem period_fiber_card (N P : ℕ) (i : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter
      (fun j => j.val % P = i.val % P)).card ≤ N / P + 1 := by
  classical
  let s := (Finset.univ : Finset (Fin N)).filter
    (fun j => j.val % P = i.val % P)
  change s.card ≤ N / P + 1
  have h := Finset.card_le_card_of_injOn
    (s := s) (t := Finset.range (N / P + 1))
    (fun j : Fin N => j.val / P)
    (by
      intro j hj
      change j.val / P ∈ Finset.range (N / P + 1)
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt j.isLt)))
    (by
      intro j hj k hk heq
      have hj' : j.val % P = i.val % P := (Finset.mem_filter.mp hj).2
      have hk' : k.val % P = i.val % P := (Finset.mem_filter.mp hk).2
      have hrem : j.val % P = k.val % P := hj'.trans hk'.symm
      apply Fin.ext
      have h1 := Nat.div_add_mod j.val P
      have h2 := Nat.div_add_mod k.val P
      rw [heq, hrem] at h1
      exact h1.symm.trans h2)
  simpa using h

/-- Absolute row sum of a collision kernel with entry M on a
matching residue pair and 0 elsewhere. -/
theorem period_row_bound (N P M : ℕ) (i : Fin N) :
    (∑ j : Fin N, if j.val % P = i.val % P then (M : ℝ) else 0) ≤
      ((N / P + 1 : ℕ) : ℝ) * M := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast period_fiber_card N P i)
    (by positivity)

/-- Uniform bound on a weighted complex collision sum. Its premises
are the exact Fourier identity from CLN02, the unit phase norm,
and the arithmetic collision criterion. -/
theorem finite_energy_bound {A R : Type*} [Fintype A] [DecidableEq R]
    (N P M : ℕ) (freq : Fin N → R) (w : Fin N → ℂ) (F : A → ℂ)
    (hw : ∀ i, ‖w i‖ = 1)
    (hcoll : ∀ i j, freq i = freq j ↔ j.val % P = i.val % P)
    (henergy : (∑ a, F a * conj (F a)) =
      ∑ i, ∑ j, (w i * conj (w j)) *
        (if freq i = freq j then (M : ℂ) else 0)) :
    (∑ a, ‖F a‖ ^ 2) ≤ (N : ℝ) * ((N / P + 1 : ℕ) : ℝ) * M := by
  classical
  have hre : (∑ a, ‖F a‖ ^ 2) = ‖∑ a, F a * conj (F a)‖ := by
    simp only [Complex.mul_conj', ← Complex.ofReal_sum, Complex.norm_real]
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun a _ => sq_nonneg ‖F a‖)]
  rw [hre, henergy]
  calc
    _ ≤ ∑ i, ‖∑ j, (w i * conj (w j)) *
        (if freq i = freq j then (M : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N,
        if j.val % P = i.val % P then (M : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ j, ‖(w i * conj (w j)) *
            (if freq i = freq j then (M : ℂ) else 0)‖ := norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          rw [hcoll]
          split_ifs with h
          · simp [norm_mul, hw]
          · simp
    _ ≤ ∑ _i : Fin N, ((N / P + 1 : ℕ) : ℝ) * M :=
      Finset.sum_le_sum fun i _ => period_row_bound N P M i
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

/-- Clear all divisions in the final collision envelope. -/
theorem scaled_energy_bound (N P M K : ℕ)
    (hMN : M ≤ N) (hMP : M ≤ K * P) :
    M * (N * (N / P + 1)) ≤ (1 + K) * N * N := by
  have hscaled : M * (N / P) ≤ K * N := by
    calc
      _ ≤ (K * P) * (N / P) := Nat.mul_le_mul_right _ hMP
      _ = K * (N / P * P) := by ring
      _ ≤ K * N := Nat.mul_le_mul_left _ (Nat.div_mul_le_self N P)
  calc
    _ = N * (M + M * (N / P)) := by ring
    _ ≤ N * (N + K * N) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add hMN hscaled)
    _ = _ := by ring

/-- The conditional second-moment bound, with the precise finite
premises explicit. N is positive so its normalization is meaningful. -/
theorem conditional_second_moment {A : Type*} [Fintype A]
    (N P M K : ℕ) (hN : 0 < N) (hMN : M ≤ N) (hMP : M ≤ K * P)
    (mass E : A → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hmass : ∀ a, mass a ≤ α) (hE : ∀ a, 0 ≤ E a)
    (henergy : (∑ a, E a) ≤ (N : ℝ) * ((N / P + 1 : ℕ) : ℝ) * M) :
    (∑ a, mass a * E a) / (N : ℝ)^2 ≤ α * (1 + (K : ℝ)) := by
  have hscale : (N : ℝ) * ((N / P + 1 : ℕ) : ℝ) * M ≤
      (1 + (K : ℝ)) * (N : ℝ) * N := by
    have h := scaled_energy_bound N P M K hMN hMP
    have h' : (↑(M * (N * (N / P + 1))) : ℝ) ≤
        ↑((1 + K) * N * N) := by exact_mod_cast h
    calc
      _ = (↑(M * (N * (N / P + 1))) : ℝ) := by push_cast; ring
      _ ≤ ↑((1 + K) * N * N) := h'
      _ = _ := by push_cast; ring
  have hw := weighted_prefix_bound mass E α hmass hE
  have hfinal := hw.trans (mul_le_mul_of_nonneg_left (henergy.trans hscale) hα)
  apply (div_le_iff₀ (by positivity : 0 < (N : ℝ)^2)).2
  convert hfinal using 1 <;> ring

#print axioms weighted_prefix_bound
#print axioms period_fiber_card
#print axioms period_row_bound
#print axioms finite_energy_bound
#print axioms scaled_energy_bound
#print axioms conditional_second_moment

end CLN03
