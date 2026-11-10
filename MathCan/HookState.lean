import Init

/-!
# CHTR-03: path-ordered hook transitions and additive holonomy

A state-changing hook has a transition `step` and an additive edge quote `q`.
For a fixed finite action word, these lemmas certify the telescoping gauge law,
closed-loop invariance, and the potential upper bound. The rate-space theorem
for all finite directed cycles is proved in the companion mathematics note
and checked by an exact rational oracle; it is not claimed as Lean-formalized.
-/
namespace MathCan.HookState

universe u v

/-- Compose market-state updates left to right. -/
def endpoint {State : Type u} {Action : Type v}
    (step : Action → State → State) (s : State) : List Action → State
  | [] => s
  | a :: xs => endpoint step (step a s) xs

/-- Accumulate state-dependent *additive* quotes along a hook word. -/
def pathSum {State : Type u} {Action : Type v}
    (step : Action → State → State) (q : Action → State → Int)
    (s : State) : List Action → Int
  | [] => 0
  | a :: xs => q a s + pathSum step q (step a s) xs

/-- Concatenating action words composes their state updates. -/
theorem endpoint_append {State : Type u} {Action : Type v}
    (step : Action → State → State) (s : State)
    (xs ys : List Action) :
    endpoint step s (xs ++ ys) = endpoint step (endpoint step s xs) ys := by
  induction xs generalizing s with
  | nil => simp [endpoint]
  | cons a rest ih => simp [endpoint, ih]

/-- The quote of a concatenation follows the updated market state. -/
theorem pathSum_append {State : Type u} {Action : Type v}
    (step : Action → State → State) (q : Action → State → Int)
    (s : State) (xs ys : List Action) :
    pathSum step q s (xs ++ ys) =
      pathSum step q s xs + pathSum step q (endpoint step s xs) ys := by
  induction xs generalizing s with
  | nil => simp [pathSum, endpoint]
  | cons a rest ih =>
      simp [pathSum, endpoint, ih, Int.add_assoc]

/-- A node gauge acts on each state-dependent quote via its target and source. -/
def gauged {State : Type u} {Action : Type v}
    (step : Action → State → State) (q : Action → State → Int)
    (p : State → Int) (a : Action) (s : State) : Int :=
  q a s + (p (step a s) - p s)

/-- Every path gauge correction telescopes exactly to its endpoint difference. -/
theorem pathSum_gauge {State : Type u} {Action : Type v}
    (step : Action → State → State) (q : Action → State → Int)
    (p : State → Int) (s : State) (xs : List Action) :
    pathSum step (gauged step q p) s xs =
      pathSum step q s xs + (p (endpoint step s xs) - p s) := by
  induction xs generalizing s with
  | nil => simp [pathSum, endpoint]
  | cons a rest ih =>
      simp only [pathSum, endpoint, gauged]
      rw [ih (step a s)]
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Path-ordered hook holonomy is gauge-invariant when state returns. -/
theorem closed_gauge_invariant {State : Type u} {Action : Type v}
    (step : Action → State → State) (q : Action → State → Int)
    (p : State → Int) (s : State) (xs : List Action)
    (hclosed : endpoint step s xs = s) :
    pathSum step (gauged step q p) s xs = pathSum step q s xs := by
  rw [pathSum_gauge, hclosed]
  simp

/-- Edgewise upper potentials bound every complete sequence of hook updates. -/
theorem pathSum_potential_bound {State : Type u} {Action : Type v}
    (step : Action → State → State) (q : Action → State → Int)
    (p : State → Int)
    (edge_bound : ∀ a s, q a s ≤ p (step a s) - p s)
    (s : State) (xs : List Action) :
    pathSum step q s xs ≤ p (endpoint step s xs) - p s := by
  induction xs generalizing s with
  | nil => simp [pathSum, endpoint]
  | cons a rest ih =>
      have ha := edge_bound a s
      have ht := ih (step a s)
      simp only [pathSum, endpoint]
      omega

/-- A closed hook sequence has nonpositive gain under a feasible potential. -/
theorem closed_path_nonpositive {State : Type u} {Action : Type v}
    (step : Action → State → State) (q : Action → State → Int)
    (p : State → Int)
    (edge_bound : ∀ a s, q a s ≤ p (step a s) - p s)
    (s : State) (xs : List Action)
    (hclosed : endpoint step s xs = s) :
    pathSum step q s xs ≤ 0 := by
  have h := pathSum_potential_bound step q p edge_bound s xs
  rw [hclosed] at h
  simpa using h

/-- An order-swap defect with matching terminal states is gauge-invariant. -/
theorem two_order_defect_gauge {State : Type u} {Action : Type v}
    (step : Action → State → State) (q : Action → State → Int)
    (p : State → Int) (s : State) (a b : Action)
    (same_endpoint : step b (step a s) = step a (step b s)) :
    pathSum step (gauged step q p) s [a, b] -
        pathSum step (gauged step q p) s [b, a] =
      pathSum step q s [a, b] - pathSum step q s [b, a] := by
  rw [pathSum_gauge, pathSum_gauge]
  simp only [endpoint]
  rw [same_endpoint]
  omega

#print axioms endpoint_append
#print axioms pathSum_append
#print axioms pathSum_gauge
#print axioms closed_gauge_invariant
#print axioms pathSum_potential_bound
#print axioms closed_path_nonpositive
#print axioms two_order_defect_gauge

end MathCan.HookState
