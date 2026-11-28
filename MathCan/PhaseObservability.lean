import Init

/-!
# SPC-06: latent-state observability and exact phase freeze

A finite formalization of the distinction between an instantaneous readout
and readouts after an update. The general real rank-growth and readout-fiber
spherical-rotation results are proved separately in SPC-06.md. These Lean
statements are exact algebraic instances, and use no external axioms.
-/

namespace MathCan.PhaseObservability

/-- A simple linear time update: the hidden coordinate enters the observable
    coordinate after one step. -/
def hiddenUpdate (s : Int × Int) : Int × Int := (0, s.1 + s.2)

def visible (s : Int × Int) : Int := s.2

/-- Two different states can have identical instantaneous readouts. -/
theorem current_readout_invisible (a : Int) :
    visible (a, 0) = visible (0, 0) := by
  rfl

/-- The same states are separated by the next readout if a is nonzero. -/
theorem next_readout_exposes_hidden (a : Int) (ha : a ≠ 0) :
    visible (hiddenUpdate (a, 0)) ≠ visible (hiddenUpdate (0, 0)) := by
  simpa [visible, hiddenUpdate] using ha

/-- A register with four independent coordinates. -/
structure Register4 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving Repr

/-- A cyclic permutation makes previously hidden coordinates visible. -/
def shift4 (s : Register4) : Register4 :=
  ⟨s.b, s.c, s.d, s.a⟩

def read4 (s : Register4) : Int := s.a

/-- Four successive scalar readouts distinguish every four-coordinate
    input, though the instantaneous readout sees one coordinate. -/
theorem four_temporal_outputs_identify_state (x y : Register4)
    (h0 : read4 x = read4 y)
    (h1 : read4 (shift4 x) = read4 (shift4 y))
    (h2 : read4 (shift4 (shift4 x)) = read4 (shift4 (shift4 y)))
    (h3 : read4 (shift4 (shift4 (shift4 x))) =
          read4 (shift4 (shift4 (shift4 y)))) : x = y := by
  cases x with
  | mk a b c d =>
    cases y with
    | mk e f g h =>
      simp only [read4, shift4] at h0 h1 h2 h3
      cases h0
      cases h1
      cases h2
      cases h3
      rfl

/-- Suppressing the first coordinate update preserves its value. -/
def freezeFirst {A C : Type} (f : A × C → A × C)
    (x : A × C) : A × C := (x.1, (f x).2)

/-- An arbitrary number of loops with the first coordinate frozen
    preserves every readout depending only on the first coordinate. -/
def iterate {S : Type} (f : S → S) : Nat → S → S
  | 0, x => x
  | n + 1, x => f (iterate f n x)

theorem frozen_coordinate_at_all_depths {A C : Type}
    (f : A × C → A × C) (n : Nat) (x : A × C) :
    (iterate (freezeFirst f) n x).1 = x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [iterate, freezeFirst] using ih

theorem frozen_readout_at_all_depths {A C Output : Type}
    (f : A × C → A × C) (readout : A → Output)
    (n : Nat) (x : A × C) :
    readout ((iterate (freezeFirst f) n x).1) = readout x.1 := by
  rw [frozen_coordinate_at_all_depths]

#print axioms current_readout_invisible
#print axioms next_readout_exposes_hidden
#print axioms four_temporal_outputs_identify_state
#print axioms frozen_coordinate_at_all_depths
#print axioms frozen_readout_at_all_depths

end MathCan.PhaseObservability
