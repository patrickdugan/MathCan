import Std

/-!
# Exact operational counterexamples

The primitive state has four addressable Boolean registers and a supplied
forward update clock. A response comparison resets an arbitrary common context
at its source event, changes that register, then applies the stated update rule.
The three-event relation below concerns these separately conducted experiments.

The truth-table results concern four independently queryable, noiseless outputs
of a Boolean function f(x,z), with index 2*z+x. They quantify over all sixteen
tables. They establish neither a spacetime limit nor a physical dimension.
-/

namespace MathCan.Pregeometry

abbrev RegisterState := Fin 4 → Bool

/-- An initial or event-local overwrite, with every other register fixed. -/
def setRegister (s : RegisterState) (i : Fin 4) (b : Bool) : RegisterState :=
  fun j => if j = i then b else s j

/-- F(x0,x1,x2,x3) = (false,x0,x0,x1 XOR x2), simultaneously. -/
def diamondStep (s : RegisterState) : RegisterState := fun j =>
  match j.val with
  | 0 => false
  | 1 => s 0
  | 2 => s 0
  | _ => s 1 ^^ s 2

def diamondSteps : Nat → RegisterState → RegisterState
  | 0, s => s
  | n + 1, s => diamondStep (diamondSteps n s)

/-- Every initial context has a zero target after two updates. -/
theorem diamond_two_step_cancellation (s : RegisterState) :
    diamondSteps 2 s 3 = false := by
  simp [diamondSteps, diamondStep]

/-- The source value is copied to the first middle register at the next tick. -/
theorem source_reaches_middle (s : RegisterState) (b : Bool) :
    diamondSteps 1 (setRegister s 0 b) 1 = b := by
  simp [diamondSteps, diamondStep, setRegister]

/-- Holding the other middle register at zero exposes the first middle input. -/
theorem middle_reaches_target (s : RegisterState) (b : Bool) :
    diamondSteps 1 (setRegister (setRegister s 2 false) 1 b) 3 = b := by
  simp [diamondSteps, diamondStep, setRegister]

/-- Clamping the second middle register after tick one restores source response. -/
theorem middle_clamp_restores_source (s : RegisterState) (b : Bool) :
    diamondStep (setRegister (diamondStep (setRegister s 0 b)) 2 false) 3 = b := by
  simp [diamondStep, setRegister]

structure ProbeEvent where
  register : Fin 4
  tick : Nat

def sourceEvent : ProbeEvent := ⟨0, 0⟩
def middleEvent : ProbeEvent := ⟨1, 1⟩
def targetEvent : ProbeEvent := ⟨3, 2⟩

/-- Each comparison permits an arbitrary context at the selected source event. -/
def EventResponse (a b : ProbeEvent) : Prop :=
  a.tick < b.tick ∧ ∃ s : RegisterState,
    diamondSteps (b.tick - a.tick) (setRegister s a.register false) b.register ≠
    diamondSteps (b.tick - a.tick) (setRegister s a.register true) b.register

theorem source_event_affects_middle : EventResponse sourceEvent middleEvent := by
  refine ⟨by decide, (fun _ => false), ?_⟩
  simp [sourceEvent, middleEvent, diamondSteps, diamondStep, setRegister]

theorem middle_event_affects_target : EventResponse middleEvent targetEvent := by
  refine ⟨by decide, (fun _ => false), ?_⟩
  simp [middleEvent, targetEvent, diamondSteps, diamondStep, setRegister]

theorem source_event_target_response_absent : ¬ EventResponse sourceEvent targetEvent := by
  intro h
  obtain ⟨_, s, hne⟩ := h
  change diamondSteps 2 (setRegister s 0 false) 3 ≠
    diamondSteps 2 (setRegister s 0 true) 3 at hne
  exact hne ((diamond_two_step_cancellation _).trans (diamond_two_step_cancellation _).symm)

/-- Nontransitivity persists for the explicitly time-labeled response relation. -/
theorem event_response_not_transitive :
    ¬ (∀ a b c, EventResponse a b → EventResponse b c → EventResponse a c) := by
  intro htrans
  exact source_event_target_response_absent
    (htrans sourceEvent middleEvent targetEvent source_event_affects_middle
      middle_event_affects_target)

abbrev TruthTable := Fin 4 → Bool

/-- Contexts are (0,1) and (2,3), following the index 2*z+x. -/
def IndependentOfX (w : TruthTable) : Prop := w 0 = w 1 ∧ w 2 = w 3

def DependsOnX (w : TruthTable) : Prop := w 0 ≠ w 1 ∨ w 2 ≠ w 3

def flipEntry (w : TruthTable) (i : Fin 4) : TruthTable :=
  fun j => if j = i then !(w j) else w j

def AgreeOn (queried : Fin 4 → Bool) (v w : TruthTable) : Prop :=
  ∀ j, queried j = true → v j = w j

theorem dependence_excludes_independence {w : TruthTable}
    (h : DependsOnX w) : ¬ IndependentOfX w := by
  intro hi
  cases h with
  | inl h01 => exact h01 hi.1
  | inr h23 => exact h23 hi.2

/-- Flipping any single entry of an independent table creates a dependence. -/
theorem flipping_independent_entry_creates_dependence
    (w : TruthTable) (hw : IndependentOfX w) (i : Fin 4) :
    DependsOnX (flipEntry w i) := by
  obtain ⟨h01, h23⟩ := hw
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · left
    simp [flipEntry, h01]
  · left
    simp [flipEntry, h01]
  · right
    simp [flipEntry, h23]
  · right
    simp [flipEntry, h23]

/-- A missing query leaves the record unchanged after that entry is flipped. -/
theorem flip_preserves_incomplete_record
    (w : TruthTable) (queried : Fin 4 → Bool) (i : Fin 4)
    (hmissing : queried i ≠ true) : AgreeOn queried (flipEntry w i) w := by
  intro j hj
  have hji : j ≠ i := by
    intro heq
    exact hmissing (heq ▸ hj)
  simp [flipEntry, hji]

/-- Every incomplete record from an independent world admits a dependent rival. -/
theorem incomplete_record_has_dependent_completion
    (w : TruthTable) (hw : IndependentOfX w) (queried : Fin 4 → Bool)
    (i : Fin 4) (hmissing : queried i ≠ true) :
    ∃ v : TruthTable, AgreeOn queried v w ∧ DependsOnX v := by
  exact ⟨flipEntry w i, flip_preserves_incomplete_record w queried i hmissing,
    flipping_independent_entry_creates_dependence w hw i⟩

/-- Certifying independence over all sixteen tables requires every entry. -/
theorem independence_certificate_requires_every_query
    (w : TruthTable) (hw : IndependentOfX w) (queried : Fin 4 → Bool)
    (hcertificate : ∀ v : TruthTable, AgreeOn queried v w → IndependentOfX v) :
    ∀ i : Fin 4, queried i = true := by
  intro i
  by_cases hi : queried i = true
  · exact hi
  · obtain ⟨v, hagree, hdep⟩ := incomplete_record_has_dependent_completion w hw queried i hi
    exact False.elim (dependence_excludes_independence hdep (hcertificate v hagree))

private theorem four_entries_require_length (queries : List (Fin 4))
    (hall : ∀ i : Fin 4, i ∈ queries) : 4 ≤ queries.length := by
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  have h3 := hall 3
  rcases queries with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h1 h2 h3
  all_goals simp only [List.length_cons, List.length_nil]
  all_goals omega

/-- A concrete query list certifying independence has length at least four.
Repeated queries are permitted. The certificate ranges over all truth tables
agreeing on each output listed in this record. -/
theorem independence_certificate_requires_four_queries
    (w : TruthTable) (hw : IndependentOfX w) (queries : List (Fin 4))
    (hcertificate : ∀ v : TruthTable,
      (∀ j, j ∈ queries → v j = w j) → IndependentOfX v) :
    4 ≤ queries.length := by
  let queried : Fin 4 → Bool := fun j => decide (j ∈ queries)
  have hcertificate' : ∀ v : TruthTable, AgreeOn queried v w → IndependentOfX v := by
    intro v hagree
    apply hcertificate v
    intro j hj
    exact hagree j (by simp [queried, hj])
  have hall : ∀ j : Fin 4, j ∈ queries := by
    intro j
    have hj := independence_certificate_requires_every_query w hw queried hcertificate' j
    exact of_decide_eq_true hj
  exact four_entries_require_length queries hall

def allZeroWorld : TruthTable := fun _ => false

def finalEntryWorld : TruthTable := flipEntry allZeroWorld 3

def firstThreeQueries : Fin 4 → Bool := fun i => decide (i.val < 3)

theorem all_zero_world_independent : IndependentOfX allZeroWorld := ⟨rfl, rfl⟩

theorem final_entry_world_dependent : DependsOnX finalEntryWorld :=
  flipping_independent_entry_creates_dependence allZeroWorld all_zero_world_independent 3

theorem first_three_queries_indistinguishable :
    AgreeOn firstThreeQueries finalEntryWorld allZeroWorld := by
  exact flip_preserves_incomplete_record allZeroWorld firstThreeQueries 3 (by decide)

theorem fourth_query_separates : finalEntryWorld 3 ≠ allZeroWorld 3 := by decide

#print axioms diamond_two_step_cancellation
#print axioms source_reaches_middle
#print axioms middle_reaches_target
#print axioms middle_clamp_restores_source
#print axioms source_event_affects_middle
#print axioms middle_event_affects_target
#print axioms source_event_target_response_absent
#print axioms event_response_not_transitive
#print axioms dependence_excludes_independence
#print axioms flipping_independent_entry_creates_dependence
#print axioms flip_preserves_incomplete_record
#print axioms incomplete_record_has_dependent_completion
#print axioms independence_certificate_requires_every_query
#print axioms independence_certificate_requires_four_queries
#print axioms all_zero_world_independent
#print axioms final_entry_world_dependent
#print axioms first_three_queries_indistinguishable
#print axioms fourth_query_separates

end MathCan.Pregeometry
