import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators
open Finset

namespace CLN06C

def grid (M J j : ℕ) : ℕ := M + j * M / J

def gridIndex (M J N : ℕ) : ℕ := J * (N - M) / M

/-- Every grid point lies in the intended source-base block. -/
theorem grid_in_block (Q M J j : ℕ)
    (hQ : 1 < Q) (hM : 0 < M) (hJ : 0 < J)
    (hj : j < (Q - 1) * J) :
    M ≤ grid M J j ∧ grid M J j < Q * M := by
  have hsplit : (Q - 1) * M + M = Q * M := by
    calc
      _ = ((Q - 1) + 1) * M := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  have hprod : j * M < ((Q - 1) * M) * J := by
    calc
      j * M < ((Q - 1) * J) * M := Nat.mul_lt_mul_of_pos_right hj hM
      _ = ((Q - 1) * M) * J := by ring
  have hq := (Nat.div_lt_iff_lt_mul hJ).2 hprod
  unfold grid
  omega

/-- The left grid point can be selected directly by a single division,
with exact finite bounds on its index and sample-size gap. -/
theorem grid_cover (Q M J N : ℕ)
    (hQ : 1 < Q) (hM : 0 < M) (hJ : 0 < J)
    (hMN : M ≤ N) (hNQ : N < Q * M) :
    let j := gridIndex M J N
    let N₀ := grid M J j
    j < (Q - 1) * J ∧ M ≤ N₀ ∧ N₀ ≤ N ∧
      J * (N - N₀) < M + J := by
  let x := N - M
  let j := J * x / M
  let q := j * M / J
  change j < (Q - 1) * J ∧ M ≤ M + q ∧ M + q ≤ N ∧
    J * (N - (M + q)) < M + J
  have hx : M + x = N := Nat.add_sub_of_le hMN
  have hsplit : (Q - 1) * M + M = Q * M := by
    calc
      _ = ((Q - 1) + 1) * M := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  have hxlt : x < (Q - 1) * M := by omega
  have hj : j < (Q - 1) * J := by
    change J * x / M < (Q - 1) * J
    apply (Nat.div_lt_iff_lt_mul hM).2
    calc
      J * x < J * ((Q - 1) * M) := Nat.mul_lt_mul_of_pos_left hxlt hJ
      _ = ((Q - 1) * J) * M := by ring
  have e₁ : j * M + (J * x) % M = J * x := Nat.div_add_mod' _ _
  have e₂ : q * J + (j * M) % J = j * M := Nat.div_add_mod' _ _
  have hqmul : q * J ≤ x * J := by rw [Nat.mul_comm x J]; omega
  have hq : q ≤ x := Nat.le_of_mul_le_mul_right hqmul hJ
  have hr₁ : (J * x) % M < M := Nat.mod_lt _ hM
  have hr₂ : (j * M) % J < J := Nat.mod_lt _ hJ
  have he : J * (x - q) + q * J = J * x := by
    rw [Nat.mul_comm q J, ← Nat.mul_add, Nat.sub_add_cancel hq]
  have hgap : N - (M + q) = x - q := by omega
  refine ⟨hj, by omega, by omega, ?_⟩
  rw [hgap]
  omega

/-- The source-base block selected by the natural logarithm has
the exact lower and upper endpoints needed for grid_cover. -/
theorem log_block (Q N : ℕ) (hQ : 1 < Q) (hN : N ≠ 0) :
    Q ^ Nat.log Q N ≤ N ∧ N < Q * Q ^ Nat.log Q N := by
  refine ⟨Nat.pow_log_le_self Q hN, ?_⟩
  simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self hQ N

section Means

variable {E : Type*} [NormedAddCommGroup E]

/-- Any block of n terms of norm at most 1 has norm at most n. -/
theorem block_sum_norm (u : ℕ → E) (hu : ∀ i, ‖u i‖ ≤ 1)
    (offset n : ℕ) :
    ‖∑ i ∈ range n, u (offset+i)‖ ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ i ∈ range n, ‖u (offset+i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range n, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => hu _
    _ = _ := by simp

/-- Real-normalized norm of partial sums. This equals the norm
of the complex Weyl average when E is the complex numbers. -/
noncomputable def meanNorm (u : ℕ → E) (n : ℕ) : ℝ :=
  ‖∑ i ∈ range n, u i‖ / (n : ℝ)

/-- Interpolate between a sample N₀ and any later sample N.
The error is the relative number of newly appended unit terms. -/
theorem mean_interpolation (u : ℕ → E) (hu : ∀ i, ‖u i‖ ≤ 1)
    (N₀ N : ℕ) (h₀ : 0 < N₀) (hN : N₀ ≤ N) :
    meanNorm u N ≤ meanNorm u N₀ + ((N - N₀ : ℕ) : ℝ) / (N : ℝ) := by
  let d := N - N₀
  have he : N₀ + d = N := Nat.add_sub_of_le hN
  have hs : (∑ i ∈ range N, u i) =
      (∑ i ∈ range N₀, u i) + ∑ i ∈ range d, u (N₀+i) := by
    calc
      _ = ∑ i ∈ range (N₀+d), u i := by rw [he]
      _ = _ := Finset.sum_range_add u N₀ d
  have hR : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast h₀
  have hR' : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) := hR.trans_le hR'
  have ht := block_sum_norm u hu N₀ d
  unfold meanNorm
  rw [hs]
  calc
    _ ≤ (‖∑ i ∈ range N₀, u i‖ +
      ‖∑ i ∈ range d, u (N₀+i)‖) / (N : ℝ) :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hpos.le
    _ = ‖∑ i ∈ range N₀, u i‖ / (N : ℝ) +
      ‖∑ i ∈ range d, u (N₀+i)‖ / (N : ℝ) := add_div _ _ _
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_left (norm_nonneg _) hR hR')
      (div_le_div_of_nonneg_right ht hpos.le)

end Means

#print axioms grid_in_block
#print axioms grid_cover
#print axioms log_block
#print axioms block_sum_norm
#print axioms mean_interpolation

end CLN06C
