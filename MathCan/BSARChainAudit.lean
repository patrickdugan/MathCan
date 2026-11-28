import Init

/-!
# BSAR-05: unbounded geometric endpoints satisfy the finite doubling-chain rules

This Init-only audit reproduces the logical shape of
`SweetbrierBSARStep7.LerayDoublingChain` at the pinned BSA-R Step 7 source:
VivienSweetbrier/bsa-r@80c62433b0eb671175bd8d6169822d3ebd922b60.

The original theorem proves a bound for each *given finite* `K`.
We show that these inductive arithmetic premises admit a family of chains
whose final states are arbitrarily large as `K` increases.

This is a countermodel to inferring a *uniform* bound from only the
inductive chain premises. It is not a Navier–Stokes counterexample, because
the external PDE-to-chain construction and total energy-budget bound are not
encoded in the inductive relation.
-/

namespace MathCan.BSARChainAudit

/-- Standalone faithful restatement of BSA-R Step7's inductive rules. -/
inductive LerayDoublingChain (M : Int) : Nat → Int → Int → Prop
  | refl (d : Int) : LerayDoublingChain M 0 d d
  | step {k : Nat} {d0 dm dnext Im : Int}
      (hprev : LerayDoublingChain M k d0 dm)
      (hdnext_nn : 0 ≤ dnext)
      (hwin_ode : M * (dnext - dm) ≤ Im * dnext)
      (hwin_half_budget : 2 * Im ≤ M) :
      LerayDoublingChain M (k + 1) d0 dnext

/-- The same recursive doubling operator used in BSA-R Step7. -/
def Pow2 : Nat → Int
  | 0 => 1
  | k + 1 => 2 * Pow2 k

/-- Integer powers of two are nonnegative. -/
private theorem power_nonneg (k : Nat) : 0 ≤ Pow2 k := by
  induction k with
  | zero => decide
  | succ k ih =>
      dsimp [Pow2]
      omega

/-- Every geometric step with M=2, Im=1 satisfies the local step premises. -/
theorem geometric_chain (k : Nat) :
    LerayDoublingChain 2 k 1 (Pow2 k) := by
  induction k with
  | zero =>
      exact LerayDoublingChain.refl 1
  | succ k ih =>
      refine LerayDoublingChain.step (Im := 1) ih ?_ ?_ ?_
      · exact power_nonneg (k + 1)
      · dsimp [Pow2]
        omega
      · decide

/-- A power of two is at least one greater than its integer index. -/
theorem power_dominates_index (k : Nat) :
    (k : Int) + 1 ≤ Pow2 k := by
  induction k with
  | zero => decide
  | succ k ih =>
      dsimp [Pow2]
      omega

/-- Arbitrarily large final chain states are consistent with these finite rules. -/
theorem chains_with_arbitrarily_large_endpoint (bound : Int) :
    ∃ k : Nat, LerayDoublingChain 2 k 1 (Pow2 k) ∧
      bound < Pow2 k := by
  refine ⟨bound.toNat, geometric_chain bound.toNat, ?_⟩
  have hb : bound ≤ (bound.toNat : Int) := by omega
  have hd := power_dominates_index bound.toNat
  omega

/-- The finite-window rule does not establish a single cap for every K. -/
theorem no_uniform_cap_from_chain_rules :
    ¬ ∃ cap : Int, ∀ k : Nat,
      LerayDoublingChain 2 k 1 (Pow2 k) →
        Pow2 k ≤ cap := by
  intro h
  obtain ⟨cap, bound⟩ := h
  obtain ⟨k, hk, hgt⟩ := chains_with_arbitrarily_large_endpoint cap
  have hc := bound k hk
  omega

end MathCan.BSARChainAudit

#print axioms MathCan.BSARChainAudit.geometric_chain
#print axioms MathCan.BSARChainAudit.power_dominates_index
#print axioms MathCan.BSARChainAudit.chains_with_arbitrarily_large_endpoint
#print axioms MathCan.BSARChainAudit.no_uniform_cap_from_chain_rules
