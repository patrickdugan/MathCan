import Init

/-!
SPC-09 finite witnesses only. State=(phase,current,deferred,inert).
The recurrent swap reveals the deferred cell next, toggles phase, and ignores
the inert cell. This file does not formalize the analytical norm/rank bounds
or certify any neural checkpoint. No native_decide or external oracle is used.
-/
namespace MathCan.CausalSubspaceCompression

abbrev State := Bool × Nat × Nat × Nat

def observe (x : State) : Nat := x.2.1
def phase (x : State) : Bool := x.1
def step (x : State) : State := (!x.1, x.2.2.1, x.2.1, 0)
def compress (x : State) : State := (x.1, x.2.1, x.2.2.1, 0)
def eraseDeferred (x : State) : State := (x.1, x.2.1, 0, x.2.2.2)

def evolve : Nat → State → State
  | 0, x => x
  | n + 1, x => step (evolve n x)

theorem compression_preserves_current (x : State) :
    observe (compress x) = observe x := by rfl

theorem compression_preserves_phase (x : State) :
    phase (compress x) = phase x := by rfl

theorem compression_commutes_after_one_step (x : State) :
    step (compress x) = step x := by rfl

theorem compression_preserves_positive_trajectory (n : Nat) (x : State) :
    evolve (n + 1) (compress x) = evolve (n + 1) x := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg step ih

theorem compression_preserves_all_observations (n : Nat) (x : State) :
    observe (evolve n (compress x)) = observe (evolve n x) := by
  cases n with
  | zero => rfl
  | succ n => exact congrArg observe (compression_preserves_positive_trajectory n x)

theorem compression_preserves_all_phases (n : Nat) (x : State) :
    phase (evolve n (compress x)) = phase (evolve n x) := by
  cases n with
  | zero => rfl
  | succ n => exact congrArg phase (compression_preserves_positive_trajectory n x)

theorem deferred_erasure_current_collision (x : State) :
    observe (eraseDeferred x) = observe x := by rfl

theorem deferred_erasure_future_difference (p : Bool) (a b c : Nat) (h : b ≠ 0) :
    observe (eraseDeferred (p, a, b, c)) = observe (p, a, b, c) ∧
    observe (step (p, a, b, c)) ≠ observe (step (eraseDeferred (p, a, b, c))) := by
  constructor
  · rfl
  · exact h

/-- A concrete Gramian perturbation: diag(1,2) to diag(1,3).
Operator norms ||O||=2, ||E||=1, ||G'-G||=5 saturate 2||O||||E||+||E||². -/
theorem finite_gramian_bound_sharp : 5 = 2 * 2 * 1 + 1 * 1 := by decide

/-- Two phases at 0 and 10: displacement four is strictly inside the half-gap. -/
theorem finite_phase_half_gap : 2 * 4 < 10 ∧ 4 < 10 - 4 := by decide

/-- Erasing a hidden value two has zero present error and next squared error four. -/
theorem finite_delayed_energy :
    observe (false, 3, 2, 7) = observe (eraseDeferred (false, 3, 2, 7)) ∧
    observe (step (false, 3, 2, 7)) * observe (step (false, 3, 2, 7)) = 4 := by
  decide

#print axioms compression_preserves_current
#print axioms compression_preserves_phase
#print axioms compression_commutes_after_one_step
#print axioms compression_preserves_positive_trajectory
#print axioms compression_preserves_all_observations
#print axioms compression_preserves_all_phases
#print axioms deferred_erasure_current_collision
#print axioms deferred_erasure_future_difference
#print axioms finite_gramian_bound_sharp
#print axioms finite_phase_half_gap
#print axioms finite_delayed_energy

end MathCan.CausalSubspaceCompression
