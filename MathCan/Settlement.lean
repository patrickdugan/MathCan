import MathCan.FundedHooks

/-!
# CHTR-05: shared-ledger settlement budgets and potential certificates

These kernel-checkable theorems concern arbitrary state-dependent registered
transitions, including before/after callbacks and arbitrary account transfers.
They treat pool lower values as explicit hypotheses. The rational AM-GM
construction used to obtain such bounds appears in the companion paper and
exact oracle; that nonlinear construction has not yet been ported to Lean.
-/

namespace MathCan.Settlement

universe u v

/-- A complete marked ledger stays constant under any sequence of locally
    conserving state-dependent updates. -/
theorem marked_total_conserved
    {State : Type u} {Action : Type v}
    (step : Action → State → State) (totalValue : State → Int)
    (locallyConserved : ∀ a s, totalValue (step a s) = totalValue s)
    (s : State) (actions : List Action) :
    totalValue (HookState.endpoint step s actions) = totalValue s := by
  exact FundedHooks.conserved_along step totalValue locallyConserved s actions

/-- Exact partition of terminal gains, including custodians, sponsors and pools.
    Every participant must be represented in exactly one of these accounts. -/
theorem exact_five_account_partition
    (trader₀ trader₁ cust₀ cust₁ sponsor₀ sponsor₁ pools₀ pools₁ : Int)
    (h : trader₁ + cust₁ + sponsor₁ + pools₁ =
         trader₀ + cust₀ + sponsor₀ + pools₀) :
    trader₁ - trader₀ = (cust₀ - cust₁) +
      (sponsor₀ - sponsor₁) + (pools₀ - pools₁) := by
  omega

/-- A lower bound on the final pooled value gives a terminal extraction budget. -/
theorem terminal_pool_floor_budget
    (gain custDraw sponsorDraw initialPool finalPool floor : Int)
    (h : gain = custDraw + sponsorDraw + initialPool - finalPool)
    (poolFloor : floor ≤ finalPool) :
    gain ≤ custDraw + sponsorDraw + initialPool - floor := by
  omega

/-- The rational/linear lower-value certificate has an *exact* residual gap,
    equal to the final pool value above its certified lower value. -/
theorem certificate_gap_identity
    (gain custDraw sponsorDraw initialPool finalPool floor : Int)
    (h : gain = custDraw + sponsorDraw + initialPool - finalPool) :
    (custDraw + sponsorDraw + initialPool - floor) - gain = finalPool - floor := by
  omega

/-- If the initial pool value is already at the certified terminal floor, a
    trader gain must be backed by a custodian/sponsor drawdown. -/
theorem protected_initial_pool_budget
    (gain custDraw sponsorDraw initialPool finalPool : Int)
    (h : gain = custDraw + sponsorDraw + initialPool - finalPool)
    (poolProtected : initialPool ≤ finalPool) :
    gain ≤ custDraw + sponsorDraw := by
  omega

/-- With no external/custodian drawdown and no aggregate pool-value decline,
    any permitted sequence has nonpositive trader gain. -/
theorem no_free_settlement_gain
    (gain custDraw sponsorDraw initialPool finalPool : Int)
    (h : gain = custDraw + sponsorDraw + initialPool - finalPool)
    (custNotDrained : custDraw ≤ 0)
    (sponsorNotDrained : sponsorDraw ≤ 0)
    (poolProtected : initialPool ≤ finalPool) :
    gain ≤ 0 := by
  omega

/-- If the trader gains without funding, an actual pool-value loss is required. -/
theorem unfunded_gain_requires_pool_loss
    (gain custDraw sponsorDraw initialPool finalPool : Int)
    (h : gain = custDraw + sponsorDraw + initialPool - finalPool)
    (custNotDrained : custDraw ≤ 0)
    (sponsorNotDrained : sponsorDraw ≤ 0)
    (profitable : 0 < gain) :
    finalPool < initialPool := by
  omega

/-- Nonnegative terminal custody and sponsor accounts bound their possible
    combined drawdown by initial prefunded inventory. -/
theorem prefunded_resource_cap
    (cust₀ cust₁ sponsor₀ sponsor₁ : Int)
    (custSolvent : 0 ≤ cust₁) (sponsorSolvent : 0 ≤ sponsor₁) :
    (cust₀ - cust₁) + (sponsor₀ - sponsor₁) ≤ cust₀ + sponsor₀ := by
  omega

/-- A reserve-value floor and terminal solvency bound *absolute* extraction by
    initial spendable funds and the initially available pool surplus. -/
theorem absolute_extraction_budget
    (gain cust₀ cust₁ sponsor₀ sponsor₁ pools₀ pools₁ floor : Int)
    (h : gain = (cust₀ - cust₁) + (sponsor₀ - sponsor₁) +
         pools₀ - pools₁)
    (custSolvent : 0 ≤ cust₁) (sponsorSolvent : 0 ≤ sponsor₁)
    (poolFloor : floor ≤ pools₁) :
    gain ≤ cust₀ + sponsor₀ + pools₀ - floor := by
  omega

/-- Sum *registered* per-action external charges along a stateful route. -/
def pathCharge {State : Type u} {Action : Type v}
    (step : Action → State → State) (charge : Action → State → Int)
    (s : State) : List Action → Int
  | [] => 0
  | a :: rest => charge a s + pathCharge step charge (step a s) rest

/-- Fundamental superpotential inequality: if every callback transition
    pays for trader gain using potential decrease plus a disclosed charge,
    the same bound holds for any adaptive finite action sequence. -/
theorem path_superpotential_bound
    {State : Type u} {Action : Type v}
    (step : Action → State → State)
    (trader potential : State → Int) (charge : Action → State → Int)
    (locallyBounded : ∀ a s,
      trader (step a s) - trader s ≤
        potential s - potential (step a s) + charge a s)
    (s : State) (actions : List Action) :
    trader (HookState.endpoint step s actions) - trader s ≤
      potential s - potential (HookState.endpoint step s actions) +
        pathCharge step charge s actions := by
  induction actions generalizing s with
  | nil => simp [HookState.endpoint, pathCharge]
  | cons a rest ih =>
      have hs := locallyBounded a s
      have ht := ih (step a s)
      simp only [HookState.endpoint, pathCharge]
      omega

/-- If terminal potential is nonnegative and the disclosed charge stays under
    a registered cap, the initial potential bounds total extraction. -/
theorem capped_superpotential_budget
    {State : Type u} {Action : Type v}
    (step : Action → State → State)
    (trader potential : State → Int) (charge : Action → State → Int)
    (locallyBounded : ∀ a s,
      trader (step a s) - trader s ≤
        potential s - potential (step a s) + charge a s)
    (s : State) (actions : List Action) (budget : Int)
    (terminalSafe : 0 ≤ potential (HookState.endpoint step s actions))
    (chargesCapped : pathCharge step charge s actions ≤ budget) :
    trader (HookState.endpoint step s actions) - trader s ≤
      potential s + budget := by
  have h := path_superpotential_bound step trader potential charge
    locallyBounded s actions
  omega

/-- A same-state loop cannot increase marked trader value without a positive
    aggregate charge under a valid local superpotential. -/
theorem closed_state_budget
    {State : Type u} {Action : Type v}
    (step : Action → State → State)
    (trader potential : State → Int) (charge : Action → State → Int)
    (locallyBounded : ∀ a s,
      trader (step a s) - trader s ≤
        potential s - potential (step a s) + charge a s)
    (s : State) (actions : List Action)
    (sameState : HookState.endpoint step s actions = s) :
    0 ≤ pathCharge step charge s actions := by
  have h := path_superpotential_bound step trader potential charge
    locallyBounded s actions
  rw [sameState] at h
  omega

#print axioms marked_total_conserved
#print axioms exact_five_account_partition
#print axioms terminal_pool_floor_budget
#print axioms certificate_gap_identity
#print axioms protected_initial_pool_budget
#print axioms no_free_settlement_gain
#print axioms unfunded_gain_requires_pool_loss
#print axioms prefunded_resource_cap
#print axioms absolute_extraction_budget
#print axioms path_superpotential_bound
#print axioms capped_superpotential_budget
#print axioms closed_state_budget

end MathCan.Settlement
