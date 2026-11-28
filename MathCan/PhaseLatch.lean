import Init

/-!
SPC-05: exact phase-shift semigroup and coordinate-local phase controls.

The kernel proves phase-transplant commutation for arbitrary deterministic
maps, coordinatewise phase-contrast arithmetic, a two-coordinate squared-
distance law, and a finite driven phase latch. The full real skew-product
contraction and dimension theorem are proved in SPC-05.md, not by Lean here.
-/

namespace MathCan.PhaseLatch

/-- A deterministic map iterated for a specified number of steps. -/
def iterStep {State : Type} (f : State → State) : Nat → State → State
  | 0, x => x
  | n + 1, x => f (iterStep f n x)

/-- Deterministic temporal dynamics compose associatively. -/
theorem iterStep_add {State : Type} (f : State → State)
    (n m : Nat) (x : State) :
    iterStep f (n + m) x = iterStep f n (iterStep f m x) := by
  induction n with
  | zero => simp [iterStep]
  | succ n ih =>
      simp only [Nat.succ_add, iterStep]
      exact congrArg f ih

/-- Starting from a future state preserves its exact time offset. -/
theorem shifted_state_remains_shifted {State : Type} (f : State → State)
    (follow shift : Nat) (x : State) :
    iterStep f follow (iterStep f shift x) =
      iterStep f shift (iterStep f follow x) := by
  calc
    iterStep f follow (iterStep f shift x) =
        iterStep f (follow + shift) x := (iterStep_add f follow shift x).symm
    _ = iterStep f (shift + follow) x := by rw [Nat.add_comm follow shift]
    _ = iterStep f shift (iterStep f follow x) := iterStep_add f shift follow x

/-- Squared Euclidean separation of two integer-coordinate states. -/
def squaredDistance (x y : Int × Int) : Int :=
  (x.1 - y.1) * (x.1 - y.1) + (x.2 - y.2) * (x.2 - y.2)

/-- A swap of the answer coordinate is separated from the future state
by the context-coordinate difference alone. -/
theorem answer_swap_distance_to_future (x y : Int × Int) :
    squaredDistance (x.1, y.2) y =
      (x.1 - y.1) * (x.1 - y.1) := by
  simp [squaredDistance]

/-- The same answer swap differs from the current state only in answer. -/
theorem answer_swap_distance_to_current (x y : Int × Int) :
    squaredDistance (x.1, y.2) x =
      (y.2 - x.2) * (y.2 - x.2) := by
  simp [squaredDistance]

/-- Squared full-state distance splits along the orthogonal blocks. -/
theorem orthogonal_phase_distance_partition (x y : Int × Int) :
    squaredDistance x y =
      squaredDistance (x.1, y.2) y + squaredDistance x (x.1, y.2) := by
  simp [squaredDistance, Int.add_comm]

/-- Whenever answer displacement dominates, the answer-transplanted
state is nearer to the next state than to the current state. -/
theorem answer_dominant_nearer_future (x y : Int × Int)
    (h : (x.1 - y.1) * (x.1 - y.1) <
         (y.2 - x.2) * (y.2 - x.2)) :
    squaredDistance (x.1, y.2) y < squaredDistance (x.1, y.2) x := by
  simpa [squaredDistance] using h

/-- Ideal phase contrasts lie in the span of differences from an anchor;
the global dimension bound of at most m is a paper-level linear algebra
corollary of this coordinatewise identity. -/
theorem phase_contrast_via_anchor {Coordinate : Type} {m : Nat}
    (code : Fin (m + 1) → Coordinate → Int)
    (i j : Fin (m + 1)) (c : Coordinate) :
    code i c - code j c =
      (code i c - code 0 c) - (code j c - code 0 c) := by
  omega

/-- Exact finite driven context: old answer drives the next context;
phase advances by negation. -/
def phaseLatchStep (s : Bool × Bool) : Bool × Bool :=
  (s.2, !s.2)

def phaseZero : Bool × Bool := (true, false)
def phaseOne : Bool × Bool := (false, true)

def swapAnswer : Bool × Bool := (phaseZero.1, phaseOne.2)
def swapContext : Bool × Bool := (phaseOne.1, phaseZero.2)

theorem latch_zero_to_one : phaseLatchStep phaseZero = phaseOne := by decide
theorem latch_one_to_zero : phaseLatchStep phaseOne = phaseZero := by decide

/-- Answer transplant advances the held-out phase after one update. -/
theorem answer_transplant_selects_next :
    phaseLatchStep swapAnswer = phaseLatchStep phaseOne := by decide

/-- Context transplant decays to the original phase in one update. -/
theorem context_transplant_retains_phase :
    phaseLatchStep swapContext = phaseLatchStep phaseZero := by decide

/-- A host-owned update can change context while suppressing the key update. -/
def suppressKeyStep {Key Context : Type}
    (f : Key × Context → Key × Context)
    (x : Key × Context) : Key × Context :=
  (x.1, (f x).2)

/-- Phase-key suppression keeps its value even if context evolves. -/
theorem suppressed_step_preserves_key {Key Context : Type}
    (f : Key × Context → Key × Context) (x : Key × Context) :
    (suppressKeyStep f x).1 = x.1 := by
  rfl

/-- For any number of later recurrence loops, the key remains frozen. -/
theorem suppressed_loops_preserve_key {Key Context : Type}
    (f : Key × Context → Key × Context) (n : Nat)
    (x : Key × Context) :
    (iterStep (suppressKeyStep f) n x).1 = x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [iterStep, suppressKeyStep] using ih

/-- Any deterministic readout depending only on that key is invariant. -/
theorem suppressed_readout_frozen {Key Context Output : Type}
    (f : Key × Context → Key × Context)
    (readout : Key → Output) (n : Nat) (x : Key × Context) :
    readout ((iterStep (suppressKeyStep f) n x).1) = readout x.1 := by
  rw [suppressed_loops_preserve_key]

#print axioms iterStep_add
#print axioms shifted_state_remains_shifted
#print axioms answer_swap_distance_to_future
#print axioms answer_swap_distance_to_current
#print axioms orthogonal_phase_distance_partition
#print axioms answer_dominant_nearer_future
#print axioms phase_contrast_via_anchor
#print axioms latch_zero_to_one
#print axioms latch_one_to_zero
#print axioms answer_transplant_selects_next
#print axioms context_transplant_retains_phase
#print axioms suppressed_step_preserves_key
#print axioms suppressed_loops_preserve_key
#print axioms suppressed_readout_frozen

end MathCan.PhaseLatch
