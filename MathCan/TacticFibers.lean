import Init

/-!
# TFH-01: structural-zero tactic fibres and Hall deficits

Pure finite mathematics inspired by openai/math results #113 (perfect-matching
entropy) and #115 (cell-bounded contingency tables). These theorems are
independent of the manuscripts' broad asymptotic claims.

A 3x3 legality pattern is a six-cycle. It admits two different perfect
matchings. Each has no legal elementary 2x2 (pair) switch, so a pair-switch
sampler started from either matching is trapped even though the full fibre
has two equally weighted configurations.

The final general and specialized arithmetic lemmas bound how much a target
family quota can exceed its reachable distinct-state capacity.
-/

namespace MathCan.TacticFibers

set_option maxRecDepth 2048
set_option maxHeartbeats 400000

/-- Six-cycle adjacency mask, with a structural zero in each row. -/
def allowed (row col : Fin 3) : Bool :=
  if row == 0 then col == 0 || col == 1
  else if row == 1 then col == 1 || col == 2
  else col == 2 || col == 0

/-- A legal 3x3 assignment uses each column exactly once. -/
def legalTriple (a b c : Fin 3) : Bool :=
  allowed 0 a && allowed 1 b && allowed 2 c &&
  (a != b) && (b != c) && (a != c)

/-- There are exactly two feasible assignments. -/
theorem exactly_two_matching_orbit :
    ∀ a b c : Fin 3, legalTriple a b c = true ↔
      ((a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 2 ∧ c = 0)) := by
  decide

/-- The first perfect matching. -/
theorem diagonal_is_legal : legalTriple 0 1 2 = true := by
  decide

/-- The other perfect matching, reached by a simultaneous 3-cycle. -/
theorem shifted_is_legal : legalTriple 1 2 0 = true := by
  decide

/-- A quota-preserving 2x2 switch swaps two assigned column choices. -/
def pairSwitchPossible (a b c : Fin 3) : Bool :=
  (allowed 0 b && allowed 1 a) ||
  (allowed 0 c && allowed 2 a) ||
  (allowed 1 c && allowed 2 b)

/-- No 2x2 switch is legal at the diagonal matching. -/
theorem diagonal_pair_switch_blocked : pairSwitchPossible 0 1 2 = false := by
  decide

/-- No 2x2 switch is legal at the other matching. -/
theorem shifted_pair_switch_blocked : pairSwitchPossible 1 2 0 = false := by
  decide

/-- An attained Hall cut bounds the minimum missing quota. -/
theorem hall_gap_monotone (quota assigned capacity : Nat)
    (hassigned : assigned ≤ capacity) (hcapacity : capacity ≤ quota) :
    quota - capacity ≤ quota - assigned := by
  omega

/-- A pair of tactic families needing 13+13 distinct examples has
    a deficit of at least 24 whenever its union of eligible training
    states has cardinality at most two. -/
theorem two_family_26_slot_deficit (assigned capacity : Nat)
    (hassigned : assigned ≤ capacity) (hcapacity : capacity ≤ 2) :
    24 ≤ 26 - assigned := by
  omega

/-- Cross-multiplied total-variation numerator for a 51-goal curriculum.
    TV >= 24/51 follows by testing the two-family event. -/
theorem fifty_one_goal_tv_numerator (assigned capacity : Nat)
    (hassigned : assigned ≤ capacity) (hcapacity : capacity ≤ 2) :
    24 * 51 ≤ (26 - assigned) * 51 := by
  omega

/-- All legal six-cycle matchings are isolated under pairwise quota-preserving
    2x2 exchanges. This enumerates all 27 triples, not just witnesses. -/
theorem every_legal_matching_pair_switch_blocked :
    ∀ a b c : Fin 3, legalTriple a b c = true →
      pairSwitchPossible a b c = false := by
  decide

/-- The frozen FC-12 four-family quota has a Hall witness consisting of
    exact_local, rcases_local, rw_local: 38 targets, at most 12 distinct
    progressing training-state neighbors. -/
theorem fc12_three_family_38_slot_deficit (assigned capacity : Nat)
    (hassigned : assigned ≤ capacity) (hcapacity : capacity ≤ 12) :
    26 ≤ 38 - assigned := by
  omega

/-- Any complete repair of this 38-slot Hall cut needs at least 26 new
    distinct training-state neighbors with compiler-verified progressing
    actions in the witness family set. -/
theorem fc12_repair_needs_26_new_neighbors (newNeighbors : Nat)
    (hfilled : 38 ≤ 12 + newNeighbors) :
    26 ≤ newNeighbors := by
  omega

/-- For a one-pass curriculum of 51 distinct states, this cross-multiplied
    inequality is the exact observed TV lower bound >= 26/51. -/
theorem fc12_exact_tv_numerator (assigned : Nat)
    (hcapacity : assigned ≤ 12) :
    26 * 51 ≤ (38 - assigned) * 51 := by
  omega

#print axioms every_legal_matching_pair_switch_blocked
#print axioms fc12_three_family_38_slot_deficit
#print axioms fc12_repair_needs_26_new_neighbors
#print axioms fc12_exact_tv_numerator
#print axioms exactly_two_matching_orbit
#print axioms diagonal_is_legal
#print axioms shifted_is_legal
#print axioms diagonal_pair_switch_blocked
#print axioms shifted_pair_switch_blocked
#print axioms hall_gap_monotone
#print axioms two_family_26_slot_deficit
#print axioms fifty_one_goal_tv_numerator

end MathCan.TacticFibers
