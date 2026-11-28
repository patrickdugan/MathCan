import Lean

namespace Galacticity

/-- Cold exact bit-probe cost envelope for independent parity blocks. -/
def coldCost (K b m : Nat) : Nat := min m K * b + m

def scanCost (b m : Nat) : Nat := m * (b + 1)

theorem coldCost_prefix (K b m : Nat) (h : m ≤ K) :
    coldCost K b m = scanCost b m := by
  simp [coldCost, scanCost, Nat.min_eq_left h, Nat.mul_add]

theorem coldCost_tail (K b m : Nat) (h : K ≤ m) :
    coldCost K b m = K * b + m := by
  simp [coldCost, Nat.min_eq_right h]

theorem affine_speedup_iff (C u v m q : Int) :
    q * (C + m * v) ≤ m * u ↔ q * C ≤ m * (u - q * v) := by
  have e₁ : q * (C + m * v) = q * C + m * (q * v) := by
    rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm q m, Int.mul_assoc]
  have e₂ : m * (u - q * v) = m * u - m * (q * v) :=
    Int.mul_sub m u (q * v)
  rw [e₁, e₂]
  omega

theorem parity_tail_iff (K b m q : Int) :
    q * (K * b + m) ≤ m * (b + 1) ↔
      q * K * b ≤ m * (b + 1 - q) := by
  simpa [Int.mul_assoc] using affine_speedup_iff (K * b) (b + 1) 1 m q

theorem no_prefix_speedup (K b m q : Nat) (hm : 0 < m)
    (hq : 1 < q) (hK : m ≤ K) :
    ¬ q * coldCost K b m ≤ scanCost b m := by
  rw [coldCost_prefix K b m hK]
  have hp : 0 < scanCost b m := by
    unfold scanCost
    exact Nat.mul_pos hm (Nat.succ_pos b)
  have hlt : 1 * scanCost b m < q * scanCost b m :=
    Nat.mul_lt_mul_of_pos_right hq hp
  rw [Nat.one_mul] at hlt
  omega

theorem no_tail_speedup_at_ceiling (K b m q : Int)
    (hK : 0 < K) (hb : 0 < b) (hm : 0 ≤ m)
    (hq : b + 1 ≤ q) :
    ¬ q * (K * b + m) ≤ m * (b + 1) := by
  rw [parity_tail_iff]
  have hq' : 0 < q := by omega
  have hl : 0 < q * K * b := Int.mul_pos (Int.mul_pos hq' hK) hb
  have hr : 0 ≤ m * (q - (b + 1)) :=
    Int.mul_nonneg hm (by omega)
  rw [Int.mul_sub] at hr
  rw [Int.mul_sub]
  omega

theorem tail_monotone (C d N m : Int) (hd : 0 ≤ d)
    (hNm : N ≤ m) (h : C ≤ N * d) : C ≤ m * d :=
  Int.le_trans h (Int.mul_le_mul_of_nonneg_right hNm hd)

theorem flip_unobserved {ι : Type} [DecidableEq ι]
    (x : ι → Bool) (S : ι → Prop) (j : ι) (hj : ¬ S j) :
    ∃ y : ι → Bool, (∀ i, S i → y i = x i) ∧ y j ≠ x j := by
  refine ⟨fun i => if i = j then !x i else x i, ?_, ?_⟩
  · intro i hi
    have h : i ≠ j := by
      intro e
      subst i
      exact hj hi
    simp [h]
  · cases h : x j <;> simp [h]

theorem admissible_monotone {α : Type} (A B : α → Prop)
    (h : ∀ a, A a → B a) (good : α → Prop) :
    (∃ a, A a ∧ good a) → ∃ a, B a ∧ good a := by
  intro hgood
  obtain ⟨a, ha, hg⟩ := hgood
  exact ⟨a, h a ha, hg⟩

end Galacticity
