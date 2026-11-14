import Init

/-!
SCT-01: exact finite SAT-core and monitor-state arithmetic.

This module formalizes the semantics of the complete eight-clause gadget
over three Boolean variables. A clause excludes exactly one of the eight
possible assignments. All eight clauses together are UNSAT; every proper
subset is satisfiable.

The two-gadget and r-gadget automaton theorems, expectation cover and
coupon hitting-time proofs have independent mathematical arguments in
Compactification Theory SCT-01. This Lean file proves finite-base
semantics and the arithmetic of its state count and radix coding.

OpenAI Math #175 and #235 are external source results. No general
Talagrand cover inequality or random-SAT threshold is formalized here.
-/

namespace MathCan.SATCoreThreshold

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- A proper three-variable signed clause, indexed by its unique false
assignment, is true on an actual assignment iff they differ. -/
def clauseTrue (forbidden actual : Fin 8) : Bool :=
  decide (forbidden ≠ actual)

/-- A set of proper three-variable clauses, encoded in eight bits. -/
def formulaTrue (mask : Fin 256) (actual : Fin 8) : Bool :=
  (List.finRange 8).all (fun forbidden =>
    !(mask.val.testBit forbidden.val) || clauseTrue forbidden actual)

/-- A complete local SAT solver that enumerates all eight assignments. -/
def satisfiable (mask : Fin 256) : Bool :=
  (List.finRange 8).any (formulaTrue mask)

/-- The eight-clause complete gadget is the unique unsatisfiable clause
subset. This is a finite 256-case kernel computation. -/
theorem three_sat_gadget_iff_proper :
    ∀ mask : Fin 256,
      satisfiable mask = decide (mask.val ≠ 255) := by
  decide

/-- The eight masks obtained by deleting exactly one of the
eight clauses of the complete gadget. -/
def sevenClauseMasks : List (Fin 256) :=
  [254, 253, 251, 247, 239, 223, 191, 127]

/-- Every immediate one-clause deletion has an available assignment. -/
theorem all_one_clause_deletions_sat :
    ∀ mask ∈ sevenClauseMasks, satisfiable mask = true := by
  decide

/-- A complete eight-clause gadget has no satisfying assignment. -/
theorem complete_gadget_unsat :
    satisfiable ⟨255, by decide⟩ = false := by
  decide

/-- The SAT status of two disjoint three-variable gadgets composes with
Boolean and. The concrete source code independently checks all 65536
subsets against all 64 joint assignments. -/
def twoGadgetSAT (left right : Fin 256) : Bool :=
  satisfiable left && satisfiable right

theorem two_gadgets_sat_iff_both_incomplete
    (left right : Fin 256) :
    twoGadgetSAT left right = true ↔
      left.val ≠ 255 ∧ right.val ≠ 255 := by
  simp [twoGadgetSAT, three_sat_gadget_iff_proper]

/-- The two-gadget monitor has 255² incomplete source supports and one
accepting state. A certifying monitor needs two accepting witness IDs. -/
theorem two_gadget_minimum_state_arithmetic :
    (255 : Nat) ^ 2 + 1 = 65026 ∧
    (255 : Nat) ^ 2 + 2 = 65027 := by
  decide

/-- Both state counts fit in sixteen bits and exceed fifteen bits. -/
theorem two_gadget_memory_bits :
    (2 : Nat) ^ 15 < 65026 ∧
    65027 ≤ (2 : Nat) ^ 16 := by
  decide

/-- Two incomplete masks can be packed as base-255 digits. -/
theorem base255_two_digit_unique
    (a b c d : Fin 255)
    (h : a.val + 255 * b.val = c.val + 255 * d.val) :
    a = c ∧ b = d := by
  have ha : a.val = c.val := by omega
  have hb : b.val = d.val := by omega
  exact ⟨Fin.ext ha, Fin.ext hb⟩

/-- Eight equally likely possible completed-core identifiers require three
fixed-length terminal bits for exact identification. -/
theorem eight_core_identifier_bits :
    (2 : Nat) ^ 2 < 8 ∧ 8 ≤ (2 : Nat) ^ 3 := by
  decide

/-- There are 511 UNSAT subsets when at least one of two disjoint complete
eight-clause cores is included. -/
theorem exact_unsat_formula_count :
    (2 : Nat) * (2 ^ 8) - 1 = 511 ∧
    (2 : Nat) ^ 16 - 511 = 65025 := by
  decide

#print axioms three_sat_gadget_iff_proper
#print axioms all_one_clause_deletions_sat
#print axioms complete_gadget_unsat
#print axioms two_gadgets_sat_iff_both_incomplete
#print axioms two_gadget_minimum_state_arithmetic
#print axioms two_gadget_memory_bits
#print axioms base255_two_digit_unique
#print axioms eight_core_identifier_bits
#print axioms exact_unsat_formula_count

end MathCan.SATCoreThreshold
