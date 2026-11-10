import MathCan.HookState

/-!
# CHTR-04: conservation and funded hook budget inequalities

Kernel-checked accounting lemmas for a state-dependent sequence of actions.
Every action can depend on current reserves, balances, and hook phase. The
per-action hypotheses demand conservation of each token, as the exact-rational
Python implementation checks for every modeled swap.

The nonlinear AMM reserve-product identity and the rational reserve-displacement
formula appear in the accompanying paper and Python oracle. The present Lean
module proves its general accounting skeleton, not those nonlinear identities.
-/

namespace MathCan.FundedHooks

universe u v

/-- A per-action conserved quantity stays conserved along any finite hook word. -/
theorem conserved_along
    {State : Type u} {Action : Type v}
    (step : Action → State → State) (quantity : State → Int)
    (one_step : ∀ a s, quantity (step a s) = quantity s)
    (s : State) (word : List Action) :
    quantity (HookState.endpoint step s word) = quantity s := by
  induction word generalizing s with
  | nil => rfl
  | cons a rest ih =>
      simp only [HookState.endpoint]
      rw [ih (step a s), one_step a s]

/-- Asset A and B conservation gives fixed-price conservation along all words. -/
theorem mark_to_market_conserved
    {State : Type u} {Action : Type v}
    (step : Action → State → State)
    (amountA amountB : State → Int)
    (conserveA : ∀ a s, amountA (step a s) = amountA s)
    (conserveB : ∀ a s, amountB (step a s) = amountB s)
    (priceA priceB : Int) (s : State) (word : List Action) :
    priceA * amountA (HookState.endpoint step s word) +
        priceB * amountB (HookState.endpoint step s word) =
      priceA * amountA s + priceB * amountB s := by
  rw [conserved_along step amountA conserveA s word,
      conserved_along step amountB conserveB s word]

/-- Conservation partitions wealth between trader, hook, and pools. -/
theorem trader_gain_exact
    (trader0 trader1 hook0 hook1 pools0 pools1 : Int)
    (conservation : trader1 + hook1 + pools1 = trader0 + hook0 + pools0) :
    trader1 - trader0 = (hook0 - hook1) - (pools1 - pools0) := by
  omega

/-- When aggregate pool marked value grows, trader gain is hook-budget bound. -/
theorem trader_gain_le_hook_drawdown
    (trader0 trader1 hook0 hook1 pools0 pools1 : Int)
    (conservation : trader1 + hook1 + pools1 = trader0 + hook0 + pools0)
    (pool_value_nondecreasing : pools0 ≤ pools1) :
    trader1 - trader0 ≤ hook0 - hook1 := by
  omega

/-- A funded hook with a nonnegative closing balance bounds absolute gain. -/
theorem trader_gain_le_initial_hook_value
    (trader0 trader1 hook0 hook1 pools0 pools1 : Int)
    (conservation : trader1 + hook1 + pools1 = trader0 + hook0 + pools0)
    (pool_value_nondecreasing : pools0 ≤ pools1)
    (funded : 0 ≤ hook1) :
    trader1 - trader0 ≤ hook0 := by
  omega

/-- Nonnegative slippage and invariant-growth gaps bound the trader's gain. -/
theorem exact_two_gap_budget
    (gain hook_drawdown displacement invariant_growth : Int)
    (h : gain = hook_drawdown - displacement - invariant_growth)
    (d_nonneg : 0 ≤ displacement)
    (k_nonneg : 0 ≤ invariant_growth) :
    gain ≤ hook_drawdown := by
  omega

/-- Under a zero hook drawdown, any positive model loss forces negative gain. -/
theorem unfinanced_strict_loss
    (gain displacement invariant_growth : Int)
    (h : gain = -displacement - invariant_growth)
    (d_nonneg : 0 ≤ displacement)
    (k_nonneg : 0 ≤ invariant_growth)
    (some_loss : 0 < displacement ∨ 0 < invariant_growth) :
    gain < 0 := by
  omega

#print axioms conserved_along
#print axioms mark_to_market_conserved
#print axioms trader_gain_exact
#print axioms trader_gain_le_hook_drawdown
#print axioms trader_gain_le_initial_hook_value
#print axioms exact_two_gap_budget
#print axioms unfinanced_strict_loss

end MathCan.FundedHooks
