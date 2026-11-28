import Lean

namespace GalacticityMarkets

/-- If the rent-or-buy threshold is never crossed, renting is optimal. -/
theorem rent_optimal (B D : Nat) (h : D ≤ B) :
    min B D = D := by
  exact Nat.min_eq_right h

/-- Once the threshold is crossed, rent already paid is below setup cost.
    This is the arithmetic certificate for a fixed-price rent-or-buy epoch. -/
theorem purchase_competitive (B D prior : Nat) (h : prior < B) (hd : B ≤ D) :
    prior + B < 2 * min B D := by
  rw [Nat.min_eq_left hd]
  omega

theorem purchase_integer_bound (B D prior : Nat) (h : prior < B) (hd : B ≤ D) :
    prior + B + 1 ≤ 2 * min B D := by
  rw [Nat.min_eq_left hd]
  omega

/-- Early purchase under a correct long-horizon prediction has cost
    <= (1 + num/den) B, stated with integer cross multiplication. -/
theorem predicted_long_consistency (B D prior num den : Nat)
    (h : den * prior ≤ num * B) (hd : B ≤ D) :
    den * (prior + B) ≤ (den + num) * min B D := by
  rw [Nat.min_eq_left hd]
  simp only [Nat.mul_add, Nat.add_mul]
  omega

/-- Independent epoch guarantees can be added. -/
theorem add_competitive (a₁ a₂ o₁ o₂ q : Nat)
    (h₁ : a₁ ≤ q * o₁) (h₂ : a₂ ≤ q * o₂) :
    a₁ + a₂ ≤ q * (o₁ + o₂) := by
  rw [Nat.mul_add]
  omega

/-- A fallback gate remains affordable if its work fits the premium on
    the current direct execution and the prior prefix was affordable. -/
theorem prefix_fallback (num den spent baseline d gate : Nat)
    (prior : den * spent ≤ (num + den) * baseline)
    (current : den * gate ≤ num * d) :
    den * (spent + (d + gate)) ≤ (num + den) * (baseline + d) := by
  simp only [Nat.mul_add, Nat.add_mul] at *
  omega

/-- A proposed action satisfying the residual scaled budget is safe. -/
theorem prefix_admit (num den spent baseline candidate : Nat)
    (prior : den * spent ≤ (num + den) * baseline)
    (affordable : den * candidate ≤ (num + den) * baseline - den * spent) :
    den * (spent + candidate) ≤ (num + den) * baseline := by
  rw [Nat.mul_add]
  omega

/-- Reserving enough work to reject a proposal safely is sufficient. -/
theorem rejection_reserve (budget direct gate evaluation proposal bound : Nat)
    (h : proposal ≤ bound)
    (reserve : direct + gate + evaluation + bound ≤ budget) :
    direct + gate + evaluation + proposal ≤ budget := by
  omega


/-- With no past savings and a strictly expensive first acquisition,
    a zero-premium prefix budget forbids the purchase. -/
theorem zero_premium_first_buy (past spent direct buy : Nat)
    (h : past ≤ spent) (extra : direct < buy) :
    ¬ spent + buy ≤ past + direct := by
  omega

/-- Before the first acquisition, the available premium must pay the
    entire excess price; prior spend is at least the direct baseline. -/
theorem first_buy_premium (num den past spent direct buy : Nat)
    (hp : past ≤ spent) (he : direct ≤ buy)
    (safe : den * (spent + buy) ≤ (num + den) * (past + direct)) :
    den * (buy - direct) ≤ num * (past + direct) := by
  have hm : den * past ≤ den * spent := Nat.mul_le_mul_left den hp
  have heq : buy - direct + direct = buy := by omega
  have hd : den * (buy - direct) + den * direct = den * buy := by
    rw [← Nat.mul_add, heq]
  simp only [Nat.mul_add, Nat.add_mul] at safe ⊢
  omega

end GalacticityMarkets
