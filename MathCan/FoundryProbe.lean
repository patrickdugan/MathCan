import MathCan.V4Transient

/-!
# CHTR-08: conditions for transporting two-currency Foundry observations

The `MathCanCHTR08.t.sol` test observes *actual* Uniswap v4-core transient
currency deltas and ERC-20 balance changes at a pinned source commit.
These lemmas characterize the mathematical consistency conditions on those
observations. They do not authenticate externally supplied JSON or establish
completeness of a raw EVM opcode trace.
-/

namespace MathCan.FoundryProbe

/-- Two observed nonzero deltas require two open transient obligations, if
    the recorded support is the complete support. -/
theorem two_nonzero_after_swap (d0 d1 observed : Int)
    (h0 : d0 ≠ 0) (h1 : d1 ≠ 0)
    (h : observed = V4Transient.count [d0, d1]) : observed = 2 := by
  simp [V4Transient.count, V4Transient.nz, h0, h1] at h
  exact h

/-- The asserted zero count after settlement forces both observed currency
    deltas to zero, if the count corresponds to this complete support. -/
theorem two_currency_zero_at_lock (d0 d1 observed : Int)
    (hCount : observed = V4Transient.count [d0, d1])
    (hZero : observed = 0) : d0 = 0 ∧ d1 = 0 := by
  have h := V4Transient.lock_zero_count [d0, d1] observed hCount hZero
  constructor
  · exact h d0 (by simp)
  · exact h d1 (by simp)

/-- Exact integer price-execution deltas settle to the opposite movements
    of manager custody for the same token. -/
theorem erc20_custody_neutral (traderBefore traderAfter vaultBefore vaultAfter delta : Int)
    (trader : traderAfter - traderBefore = delta)
    (manager : vaultAfter - vaultBefore = -delta) :
    traderAfter + vaultAfter = traderBefore + vaultBefore := by
  omega

/-- Each of the two traded ERC-20 currencies is individually conserved. -/
theorem both_erc20_currencies_conserved
    (trader0Before trader0After vault0Before vault0After
     trader1Before trader1After vault1Before vault1After delta0 delta1 : Int)
    (t0 : trader0After - trader0Before = delta0)
    (v0 : vault0After - vault0Before = -delta0)
    (t1 : trader1After - trader1Before = delta1)
    (v1 : vault1After - vault1Before = -delta1) :
    trader0After + vault0After = trader0Before + vault0Before ∧
    trader1After + vault1After = trader1Before + vault1Before := by
  constructor
  · exact erc20_custody_neutral _ _ _ _ _ t0 v0
  · exact erc20_custody_neutral _ _ _ _ _ t1 v1

/-- If the returned caller delta agrees with the emitted Swap delta, that
    emission also agrees with the actual trader ERC-20 movement. -/
theorem swap_log_trader_consistency (emitted returned before after : Int)
    (event : emitted = returned)
    (movement : after - before = returned) :
    after - before = emitted := by
  omega

/-- The two observations on either side of the unlock witness have the
    expected open-count transition, under the complete-support hypothesis. -/
theorem nonzero_counter_probe (d0 d1 before afterSwap afterSettle : Int)
    (d0nz : d0 ≠ 0) (d1nz : d1 ≠ 0)
    (beforeZero : before = V4Transient.count [0, 0])
    (swapCount : afterSwap = V4Transient.count [d0, d1])
    (settleCount : afterSettle = V4Transient.count [0, 0]) :
    before = 0 ∧ afterSwap = 2 ∧ afterSettle = 0 := by
  constructor
  · simpa [V4Transient.count, V4Transient.nz] using beforeZero
  constructor
  · exact two_nonzero_after_swap d0 d1 afterSwap d0nz d1nz swapCount
  · simpa [V4Transient.count, V4Transient.nz] using settleCount

/-- ERC-20 balance-conservation witnesses compose over a finite list of
    observed swaps (including hook-dependent orderings). -/
theorem custody_conserved_along_observations (pairs : List (Int × Int))
    (h : ∀ p ∈ pairs, p.1 + p.2 = 0) :
    (pairs.map fun p => p.1 + p.2).sum = 0 := by
  induction pairs with
  | nil => simp
  | cons p rest ih =>
      have hp : p.1 + p.2 = 0 := h p (by simp)
      have hr : ∀ x ∈ rest, x.1 + x.2 = 0 := by
        intro x hx
        exact h x (by simp [hx])
      simp only [List.map_cons, List.sum_cons, hp]
      simp [ih hr]

#print axioms two_nonzero_after_swap
#print axioms two_currency_zero_at_lock
#print axioms erc20_custody_neutral
#print axioms both_erc20_currencies_conserved
#print axioms swap_log_trader_consistency
#print axioms nonzero_counter_probe
#print axioms custody_conserved_along_observations

end MathCan.FoundryProbe
