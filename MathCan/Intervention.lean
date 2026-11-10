import Init

/-!
# MathCan: finite intervention-relative equivalence

These elementary, kernel-checkable lemmas formalize the logical interface
monotonicity of LVR-01. The bounded-horizon stochastic TV result is proved
on paper and tested as a finite rational oracle; it is not formalized here.
-/
namespace MathCan

universe u v w z

/-- Apply an action word from left to right. -/
def runActions {State : Type u} {Action : Type v}
    (step : Action → State → State) (word : List Action) (state : State) : State :=
  word.foldl (fun s a => step a s) state

/-- Behavioral equivalence relative to an action predicate and observable. -/
def obsEqOn {State : Type u} {Action : Type v} {Obs : Type w}
    (allowed : Action → Prop) (step : Action → State → State)
    (readout : State → Obs) (s t : State) : Prop :=
  ∀ word : List Action, (∀ a, a ∈ word → allowed a) →
    readout (runActions step word s) = readout (runActions step word t)

theorem obsEqOn_refl {State : Type u} {Action : Type v} {Obs : Type w}
    (allowed : Action → Prop) (step : Action → State → State)
    (readout : State → Obs) (s : State) :
    obsEqOn allowed step readout s s := by
  intro word valid
  rfl

theorem obsEqOn_symm {State : Type u} {Action : Type v} {Obs : Type w}
    (allowed : Action → Prop) (step : Action → State → State)
    (readout : State → Obs) {s t : State}
    (h : obsEqOn allowed step readout s t) :
    obsEqOn allowed step readout t s := by
  intro word valid
  exact (h word valid).symm

theorem obsEqOn_trans {State : Type u} {Action : Type v} {Obs : Type w}
    (allowed : Action → Prop) (step : Action → State → State)
    (readout : State → Obs) {s t r : State}
    (hst : obsEqOn allowed step readout s t)
    (htr : obsEqOn allowed step readout t r) :
    obsEqOn allowed step readout s r := by
  intro word valid
  exact (hst word valid).trans (htr word valid)

/-- Widening the action menu refines behavioral equivalence. -/
theorem obsEqOn_action_subset
    {State : Type u} {Action : Type v} {Obs : Type w}
    (small large : Action → Prop) (step : Action → State → State)
    (readout : State → Obs) {s t : State}
    (inclusion : ∀ a, small a → large a)
    (h : obsEqOn large step readout s t) :
    obsEqOn small step readout s t := by
  intro word valid
  apply h word
  intro a ha
  exact inclusion a (valid a ha)

/-- A coarser readout preserves all equalities witnessed by a finer readout. -/
theorem obsEqOn_postcompose
    {State : Type u} {Action : Type v} {Fine : Type w} {Coarse : Type z}
    (allowed : Action → Prop) (step : Action → State → State)
    (fine : State → Fine) (coarsen : Fine → Coarse) {s t : State}
    (h : obsEqOn allowed step fine s t) :
    obsEqOn allowed step (fun x => coarsen (fine x)) s t := by
  intro word valid
  exact congrArg coarsen (h word valid)

/-- Behavioral equivalence is stable under any permitted one-step action. -/
theorem obsEqOn_action_stable
    {State : Type u} {Action : Type v} {Obs : Type w}
    (allowed : Action → Prop) (step : Action → State → State)
    (readout : State → Obs) {s t : State}
    (h : obsEqOn allowed step readout s t)
    (a : Action) (ha : allowed a) :
    obsEqOn allowed step readout (step a s) (step a t) := by
  intro word valid
  have validAll : ∀ b, b ∈ (a :: word) → allowed b := by
    intro b hb
    have hb' : b = a ∨ b ∈ word := List.mem_cons.mp hb
    cases hb' with
    | inl hEq =>
        subst b
        exact ha
    | inr hMem => exact valid b hMem
  simpa [runActions] using (h (a :: word) validAll)

#print axioms obsEqOn_refl
#print axioms obsEqOn_symm
#print axioms obsEqOn_trans
#print axioms obsEqOn_action_subset
#print axioms obsEqOn_postcompose
#print axioms obsEqOn_action_stable

end MathCan
