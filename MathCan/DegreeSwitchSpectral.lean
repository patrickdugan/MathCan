import Init

/-!
# DSC-01: degree-preserving topology camouflage

This is an exact finite Lean/Init companion to Control-Harness DSC-01
(OpenAI Math #131 × #178). It formalizes the concrete cubic eight-node
three-switch path and indistinguishable degree lists. The large-n
spectral construction, the 70-state Markov mixing theorem, and the
general first-/second-order probe law remain in the primary paper
and its exact Fraction reference, not in this Lean file.

Graph edge bit ordering is lexicographic:
(0,1),(0,2),...,(0,7),(1,2),...,(6,7).
-/

namespace MathCan.DegreeSwitchSpectral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def pairs8 : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),
   (1,2),(1,3),(1,4),(1,5),(1,6),(1,7),
   (2,3),(2,4),(2,5),(2,6),(2,7),
   (3,4),(3,5),(3,6),(3,7),
   (4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

/-- Degree of vertex v in the unsigned 28-bit simple graph. -/
def degree8 (mask v : Nat) : Nat :=
  ((List.range 28).zip pairs8).foldl
    (fun acc edge =>
      if mask.testBit edge.1 &&
        (edge.2.1 == v || edge.2.2 == v) then acc + 1 else acc) 0

/-- Two disjoint four-vertex cliques: 2K4. -/
def twoK4 : Nat := 264249735

/-- Reversible sequence through three degree-preserving 2-switches. -/
def stepOne : Nat := 255926669
def stepTwo : Nat := 239411657
def mobiusEight : Nat := 174400713

/-- XOR the four edge bits that a legitimate switch replaces. -/
def flipFour (mask a b c d : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor mask (2^a)) (2^b)) (2^c)) (2^d)

/-- Remove (0,2),(4,6); add (0,4),(2,6). -/
theorem switch_one :
    flipFour twoK4 1 23 3 16 = stepOne := by decide

/-- Remove (0,3),(4,7); add (0,7),(3,4). -/
theorem switch_two :
    flipFour stepOne 2 24 6 18 = stepTwo := by decide

/-- Remove (1,3),(5,7); add (1,5),(3,7). -/
theorem switch_three :
    flipFour stepTwo 8 26 10 21 = mobiusEight := by decide

/-- Every state on the exact 3-switch path retains degree three. -/
theorem all_switch_states_cubic :
    ∀ v ∈ List.range 8,
      degree8 twoK4 v = 3 ∧
      degree8 stepOne v = 3 ∧
      degree8 stepTwo v = 3 ∧
      degree8 mobiusEight v = 3 := by
  decide

/-- Both distinct graphs produce the identical degree telemetry. -/
theorem same_degree_observation :
    (List.range 8).map (degree8 twoK4) =
      (List.range 8).map (degree8 mobiusEight) := by
  decide

/-- A controller whose input is only the degree vector returns
the same output under either hidden graph world. -/
theorem degree_only_decoder_cannot_separate
    {Decision : Type} (controller : List Nat → Decision) :
    controller ((List.range 8).map (degree8 twoK4)) =
    controller ((List.range 8).map (degree8 mobiusEight)) := by
  rw [same_degree_observation]

/-- Total number of edges between the two four-vertex halves. -/
def crossEdges (mask : Nat) : Nat :=
  ((List.range 28).zip pairs8).foldl
    (fun acc edge =>
      if mask.testBit edge.1 &&
        ((edge.2.1 < 4 && 4 ≤ edge.2.2) ||
         (edge.2.2 < 4 && 4 ≤ edge.2.1)) then acc + 1 else acc) 0

/-- The two cubic graphs differ in a global connectivity-relevant cut. -/
theorem twoK4_has_no_cross_edges : crossEdges twoK4 = 0 := by decide
theorem mobius_has_six_cross_edges : crossEdges mobiusEight = 6 := by decide

/-- Each side of the two-clique witness really is internally K4. -/
theorem twoK4_has_twelve_edges :
    ((List.range 28).filter (fun i => twoK4.testBit i)).length = 12 := by
  decide

/-- Both graphs have the same number of edges after the switches. -/
theorem mobius_has_twelve_edges :
    ((List.range 28).filter (fun i => mobiusEight.testBit i)).length = 12 := by
  decide

#print axioms switch_one
#print axioms switch_two
#print axioms switch_three
#print axioms all_switch_states_cubic
#print axioms same_degree_observation
#print axioms degree_only_decoder_cannot_separate
#print axioms twoK4_has_no_cross_edges
#print axioms mobius_has_six_cross_edges
#print axioms twoK4_has_twelve_edges
#print axioms mobius_has_twelve_edges

end MathCan.DegreeSwitchSpectral
