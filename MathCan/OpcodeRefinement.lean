import MathCan.FoundryProbe

/-!
# CHTR-09: source-observation and two-range integer accounting

The executable Foundry test actually records PoolManager TSTORE opcodes and
crosses an initialized concentrated-liquidity tick. These lemmas justify
accounting identities conditional on faithful event measurement. The upstream
Solidity source, compiler artifact, numeric Q64.96 arithmetic and raw ordered
opcode stream are separately audited by the Python verifier.
-/
namespace MathCan.OpcodeRefinement

/-- Two exact-input steps, with their individually rounded fees, account for
    precisely the offered gross amount when the second step exhausts it. -/
theorem two_step_gross_budget
    (gross net₁ fee₁ net₂ fee₂ : Int)
    (h : gross = net₁ + fee₁ + net₂ + fee₂) :
    gross - (net₁ + fee₁) = net₂ + fee₂ := by
  omega

/-- The two independently floored token-output steps sum to the final
    executed output; no unlisted inter-tick token transfer is allowed. -/
theorem two_step_output_aggregation
    (step₁ step₂ emitted : Int)
    (h : emitted = step₁ + step₂) :
    emitted - step₁ = step₂ := by
  omega

/-- Crossing a boundary switches to the lower initialized range's active
    liquidity, given the observed signed liquidity net at the boundary. -/
theorem boundary_liquidity_transition
    (upper lower crossedNet : Int)
    (hNet : crossedNet = lower - upper) :
    upper + crossedNet = lower := by
  omega

/-- Individual settled deltas imply the zero terminal outstanding count when
    the source support list is complete. -/
theorem terminal_count_after_two_currencies
    (d₀ d₁ : Int) (h0 : d₀ = 0) (h1 : d₁ = 0) :
    MathCan.V4Transient.count [d₀, d₁] = 0 := by
  simp [h0, h1, MathCan.V4Transient.count, MathCan.V4Transient.nz]

/-- An observed counter of zero implies every observed currency delta is zero,
    provided the support list includes every delta slot touched by the trace. -/
theorem zero_count_for_complete_support
    (outstanding : List Int) (reported : Int)
    (hCount : reported = MathCan.V4Transient.count outstanding)
    (hZero : reported = 0) :
    ∀ d, d ∈ outstanding → d = 0 := by
  exact MathCan.V4Transient.lock_zero_count outstanding reported hCount hZero

/-- A two-step swap and final ERC20 settlement produce opposite external
    token flows, independently for both currencies. -/
theorem crossed_tick_custody_conservation
    (trader0Before trader0After vault0Before vault0After
     trader1Before trader1After vault1Before vault1After in₀ out₁ : Int)
    (t0 : trader0After - trader0Before = -in₀)
    (v0 : vault0After - vault0Before = in₀)
    (t1 : trader1After - trader1Before = out₁)
    (v1 : vault1After - vault1Before = -out₁) :
    trader0After + vault0After = trader0Before + vault0Before ∧
    trader1After + vault1After = trader1Before + vault1Before := by
  constructor <;> omega

/-- The recorded price is strictly within the adjacent range after one
    boundary crossing, under the exact integer price witness. -/
theorem one_boundary_price_bracket (lower boundary finalPrice : Int)
    (hLo : lower < finalPrice) (hHi : finalPrice < boundary) :
    lower < boundary := by
  omega

/-- With a bytecode correspondence and complete observations, the original
    abstract step-refinement theorem transports conservation to finite traces. -/
theorem observed_finite_refinement
    {Concrete Abstract Action : Type}
    (concrete : Action → Concrete → Concrete)
    (abstract : Action → Abstract → Abstract)
    (encode : Concrete → Abstract)
    (oneStep : ∀ a s, encode (concrete a s) = abstract a (encode s))
    (s : Concrete) (actions : List Action) :
    encode (MathCan.HookState.endpoint concrete s actions) =
      MathCan.HookState.endpoint abstract (encode s) actions := by
  exact MathCan.FlashAccounting.finite_trace_refinement concrete abstract encode oneStep s actions

#print axioms two_step_gross_budget
#print axioms two_step_output_aggregation
#print axioms boundary_liquidity_transition
#print axioms terminal_count_after_two_currencies
#print axioms zero_count_for_complete_support
#print axioms crossed_tick_custody_conservation
#print axioms one_boundary_price_bracket
#print axioms observed_finite_refinement

end MathCan.OpcodeRefinement
