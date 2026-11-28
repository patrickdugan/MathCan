import Mathlib

namespace Galacticity

/-- Cold exact bit-probe cost envelope for the independent parity-block model.
    The semantic adversary argument is in research/galacticity/README.md. -/
def coldCost (K b m : ℕ) : ℕ := min m K * b + m

def scanCost (b m : ℕ) : ℕ := m * (b + 1)

theorem coldCost_prefix (K b m : ℕ) (h : m ≤ K) :
    coldCost K b m = scanCost b m := by
  unfold coldCost scanCost
  rw [min_eq_left h, Nat.mul_add, Nat.mul_one]

theorem coldCost_tail (K b m : ℕ) (h : K ≤ m) :
    coldCost K b m = K * b + m := by
  unfold coldCost
  rw [min_eq_right h]

/-- Integer algebra isolates the amortization barrier. -/
theorem affine_speedup_iff (C u v m q : ℤ) :
    q * (C + m * v) ≤ m * u ↔ q * C ≤ m * (u - q * v) := by
  have e : m * (u - q * v) = m * u - q * (m * v) := by ring
  rw [e, mul_add]
  omega

theorem parity_tail_iff (K b m q : ℤ) :
    q * (K * b + m) ≤ m * (b + 1) ↔
      q * K * b ≤ m * (b + 1 - q) := by
  have e₁ : q * (K * b + m) = q * K * b + q * m := by ring
  have e₂ : m * (b + 1 - q) = m * (b + 1) - q * m := by ring
  rw [e₁, e₂]
  omega

theorem no_prefix_speedup (K b m q : ℕ) (hm : 0 < m)
    (hq : 1 < q) (hK : m ≤ K) :
    ¬ q * coldCost K b m ≤ scanCost b m := by
  rw [coldCost_prefix K b m hK]
  have hp : 0 < scanCost b m := by
    unfold scanCost
    exact Nat.mul_pos hm (Nat.succ_pos b)
  have hlt : 1 * scanCost b m < q * scanCost b m :=
    Nat.mul_lt_mul_of_pos_right hq hp
  rw [one_mul] at hlt
  omega

theorem no_tail_speedup_at_ceiling (K b m q : ℤ)
    (hK : 0 < K) (hb : 0 < b) (hm : 0 ≤ m)
    (hq : b + 1 ≤ q) :
    ¬ q * (K * b + m) ≤ m * (b + 1) := by
  rw [parity_tail_iff]
  have hq' : 0 < q := by omega
  have hl : 0 < q * K * b := mul_pos (mul_pos hq' hK) hb
  have hr : m * (b + 1 - q) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hm (by omega)
  omega

/-- A proposed threshold survives all later horizons if delta is nonnegative. -/
theorem tail_monotone (C d N m : ℤ) (hd : 0 ≤ d)
    (hNm : N ≤ m) (h : C ≤ N * d) : C ≤ m * d :=
  le_trans h (mul_le_mul_of_nonneg_right hNm hd)

/-- Local indistinguishability: changing a bit outside the observation set
    preserves all observed bits while changing the target bit. This is the
    primitive used in the semantic parity adversary, not a full machine model. -/
theorem flip_unobserved {ι : Type*} [DecidableEq ι]
    (x : ι → Bool) (S : Set ι) (j : ι) (hj : j ∉ S) :
    ∃ y : ι → Bool, (∀ i ∈ S, y i = x i) ∧ y j ≠ x j := by
  refine ⟨fun i => if i = j then !x i else x i, ?_, ?_⟩
  · intro i hi
    have h : i ≠ j := by
      intro e
      subst i
      exact hj hi
    simp [h]
  · cases h : x j <;> simp [h]

/-- A wider admissible family cannot remove a witness. -/
theorem admissible_monotone {α : Type*} (A B : Set α)
    (h : A ⊆ B) (good : α → Prop) :
    (∃ a ∈ A, good a) → ∃ a ∈ B, good a := by
  rintro ⟨a, ha, hg⟩
  exact ⟨a, h ha, hg⟩

end Galacticity
