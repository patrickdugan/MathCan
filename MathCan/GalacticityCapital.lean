import Lean

namespace GalacticityCapital

/-- Pay before receiving the savings. This is the one-step Bellman inverse. -/
theorem required_seed_iff (capital cost savings future : Nat) :
    (cost ≤ capital ∧ future ≤ capital - cost + savings) ↔
      cost + (future - savings) ≤ capital := by
  omega

theorem required_seed_feasible (cost savings future : Nat) :
    cost ≤ cost + (future - savings) ∧
    future ≤ (cost + (future - savings)) - cost + savings := by
  apply (required_seed_iff _ _ _ _).mpr
  omega

/-- Greater capital never hurts when the state and future actions agree. -/
theorem step_dominance (low high cost savings : Nat)
    (h : low ≤ high) (afford : cost ≤ low) :
    cost ≤ high ∧ low - cost + savings ≤ high - cost + savings := by
  omega

/-- Capital summary as a pair of inequalities, avoiding real arithmetic. -/
def Feasible (need gain capital final : Int) : Prop :=
  need ≤ capital ∧ final = capital + gain

theorem composition_spec (n₁ g₁ n₂ g₂ capital final : Int) :
    (∃ middle, Feasible n₁ g₁ capital middle ∧
      Feasible n₂ g₂ middle final) ↔
    (n₁ ≤ capital ∧ n₂ - g₁ ≤ capital ∧
      final = capital + (g₁ + g₂)) := by
  constructor
  · intro h
    obtain ⟨middle, h₁, h₂⟩ := h
    unfold Feasible at h₁ h₂
    omega
  · intro h
    refine ⟨capital + g₁, ?_, ?_⟩
    · unfold Feasible
      omega
    · unfold Feasible
      omega

/-- All three funding inequalities are independent of parenthesization. -/
theorem triple_funding (n₁ g₁ n₂ g₂ n₃ capital : Int) :
    (n₁ ≤ capital ∧ n₂ ≤ capital + g₁ ∧
      n₃ ≤ (capital + g₁) + g₂) ↔
    (n₁ ≤ capital ∧ n₂ - g₁ ≤ capital ∧
      n₃ - (g₁ + g₂) ≤ capital) := by
  omega

/-- Adjacent exchange of profitable investments, low cost first. -/
theorem exchange_profitable (a b ra rb capital : Int)
    (hab : a ≤ b) (ha : a ≤ ra) (hb : b ≤ rb)
    (reverse : b ≤ capital ∧ a ≤ capital + (rb - b)) :
    a ≤ capital ∧ b ≤ capital + (ra - a) := by omega

/-- Adjacent exchange of loss-making investments, high return first. -/
theorem exchange_loss (a b ra rb capital : Int)
    (ha : ra ≤ a) (hb : rb ≤ b) (hr : rb ≤ ra)
    (reverse : b ≤ capital ∧ a ≤ capital + (rb - b)) :
    a ≤ capital ∧ b ≤ capital + (ra - a) := by omega

/-- A profitable investment may be moved before a loss-making investment. -/
theorem exchange_mixed (a b ra rb capital : Int)
    (ha : a ≤ ra) (hb : rb ≤ b)
    (reverse : b ≤ capital ∧ a ≤ capital + (rb - b)) :
    a ≤ capital ∧ b ≤ capital + (ra - a) := by omega

/-- If the mandatory future set is already too large, no monotone
    extension of the retained portfolio can meet the same cap. -/
theorem persistent_capacity_obstruction (used mandatory extra cap : Nat)
    (tooLarge : cap < used + mandatory) :
    cap < used + mandatory + extra := by omega

end GalacticityCapital
