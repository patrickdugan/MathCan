import Init

/-!
# SPC-08: present-output blindness and delayed finite-state recovery

An Init-only kernel witness for the distinction between the current
readout and future readouts of a recurrent state. The generic rank identity
and Gramian covariance in the companion paper are finite-dimensional linear
algebra statements, and are NOT claimed as Lean theorems in this file.

The two- and three-coordinate cyclic registers are exact sharp examples:
they hide coordinates from the current observation, and subsequent
recurrence visits expose them without accessing an extra input.
-/

namespace MathCan.DeferredObservability

/-- The current scalar observation of a two-cell register. -/
def observe2 (x : Nat × Nat) : Nat := x.1

/-- A cyclic two-cell recurrence. -/
def step2 (x : Nat × Nat) : Nat × Nat := (x.2, x.1)

/-- At time zero, changing the hidden cell leaves the current output fixed. -/
theorem present_blind_to_second (a b c : Nat) :
    observe2 (a, b) = observe2 (a, c) := by
  rfl

/-- One recurrent update reveals the hidden second coordinate exactly. -/
theorem next_observation_is_hidden (a b : Nat) :
    observe2 (step2 (a, b)) = b := by
  rfl

/-- A distinct hidden coordinate is a delayed-only distinguishing witness. -/
theorem delayed_separation (a b c : Nat) (h : b ≠ c) :
    observe2 (a, b) = observe2 (a, c) ∧
    observe2 (step2 (a, b)) ≠ observe2 (step2 (a, c)) := by
  constructor
  · rfl
  · simpa [observe2, step2] using h

/-- Two consecutive scalar observations reconstruct the full register. -/
def trace2 (x : Nat × Nat) : Nat × Nat :=
  (observe2 x, observe2 (step2 x))

theorem trace2_identity (x : Nat × Nat) : trace2 x = x := by
  cases x with
  | mk a b => rfl

theorem trace2_separates {x y : Nat × Nat} (h : trace2 x = trace2 y) : x = y := by
  calc
    x = trace2 x := (trace2_identity x).symm
    _ = trace2 y := h
    _ = y := trace2_identity y

/-- A width-three cyclic register, exposing one coordinate per loop. -/
def step3 (x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (x.2.1, x.2.2, x.1)

def observe3 (x : Nat × Nat × Nat) : Nat := x.1

/-- The full three-time observation record. -/
def trace3 (x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (observe3 x, observe3 (step3 x), observe3 (step3 (step3 x)))

/-- The three successive outputs reproduce all three hidden coordinates. -/
theorem trace3_identity (x : Nat × Nat × Nat) : trace3 x = x := by
  cases x with
  | mk a bc =>
      cases bc with
      | mk b c => rfl

/-- Exact injectivity of the temporal observation record. -/
theorem trace3_separates {x y : Nat × Nat × Nat}
    (h : trace3 x = trace3 y) : x = y := by
  calc
    x = trace3 x := (trace3_identity x).symm
    _ = trace3 y := h
    _ = y := trace3_identity y

/-- Instantaneous output ignores the two trailing latent coordinates. -/
theorem three_cell_current_collision (a b c d e : Nat) :
    observe3 (a, b, c) = observe3 (a, d, e) := by
  rfl

/-- The next-loop observation distinguishes the second coordinate. -/
theorem three_cell_one_step_difference (a b c d e : Nat) (h : b ≠ d) :
    observe3 (step3 (a, b, c)) ≠ observe3 (step3 (a, d, e)) := by
  simpa [observe3, step3] using h

/-- The second future observation distinguishes the third coordinate. -/
theorem three_cell_two_step_difference (a b c d e : Nat) (h : c ≠ e) :
    observe3 (step3 (step3 (a, b, c))) ≠
      observe3 (step3 (step3 (a, d, e))) := by
  simpa [observe3, step3] using h

#print axioms present_blind_to_second
#print axioms next_observation_is_hidden
#print axioms delayed_separation
#print axioms trace2_identity
#print axioms trace2_separates
#print axioms trace3_identity
#print axioms trace3_separates
#print axioms three_cell_current_collision
#print axioms three_cell_one_step_difference
#print axioms three_cell_two_step_difference

end MathCan.DeferredObservability
