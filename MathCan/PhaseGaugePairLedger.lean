import Init

/-!
COE-07: pairwise discriminator loss under hierarchical observer quotients.

The paper proves the full graph-collision formula and optimal balanced
necklace allocations. Here Lean establishes the pair-count merge identity,
exact telescoping of ordered/cyclic/count collisions, and finite arithmetic
receipts. Native LoopScope data are not imported as axioms.
-/
namespace MathCan.PhaseGaugePairLedger

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The number of unordered pairs in a group of size n, defined recursively
    without division or any untrusted computation. -/
def pairs : Nat → Nat
  | 0 => 0
  | n + 1 => pairs n + n

/-- Merging two disjoint color classes produces exactly a*b new collisions.
    This is the combinatorial atom of the phase-quotient loss formula. -/
theorem pairs_add (a b : Nat) :
    pairs (a + b) = pairs a + pairs b + a * b := by
  induction b with
  | zero =>
      simp [pairs]
  | succ b ih =>
      calc
        pairs (a + (b + 1)) = pairs (a + b) + (a + b) := by
          rfl
        _ = (pairs a + pairs b + a * b) + (a + b) := by
          rw [ih]
        _ = pairs a + pairs (b + 1) + a * (b + 1) := by
          simp only [pairs, Nat.mul_succ]
          omega

/-- The additional collision cost of a single class merge is a*b. -/
theorem merge_collision_gap (a b : Nat) :
    pairs (a + b) - (pairs a + pairs b) = a * b := by
  rw [pairs_add]
  omega

/-- Given the nested collision counts from ordered histories, necklaces,
    and popcounts, the retained-pair ledger telescopes exactly. -/
theorem phase_quotient_ledger (total orderedCollision cyclicCollision countCollision : Nat)
    (hoc : orderedCollision ≤ cyclicCollision)
    (hcc : cyclicCollision ≤ countCollision)
    (hct : countCollision ≤ total) :
    total - orderedCollision =
      (total - countCollision) +
      (countCollision - cyclicCollision) +
      (cyclicCollision - orderedCollision) := by
  omega

/-- Eight visits and nine labels give thirty-six possible K9 pairs. -/
theorem nine_label_pairs : pairs 9 = 36 := by decide

/-- Sixty-four labels have 2016 unordered pairs before the digit-equality
    exclusions used by the empirical benchmark. -/
theorem sixty_four_pairs : pairs 64 = 2016 := by decide

/-- The observed 8-step S4 oracle counts are consistent with the algebraic
    telescope; this is integer arithmetic, not a kernel proof of the source. -/
theorem s4_stalled_eight_visit_arithmetic :
    1414 = 1389 + 25 ∧
    1389 = 1369 + 20 ∧
    1369 ≤ 1795 := by decide

/-- Prior four-visit stalled-board output ledger, 64 boards, distinct digits. -/
theorem s4_stalled_four_visit_arithmetic :
    1278 = 1244 + 34 ∧
    1244 = 1244 + 0 ∧
    1244 ≤ 1795 := by decide

/-- Extended sixteen-visit stalled-board output ledger, same 64 boards. -/
theorem s4_stalled_sixteen_visit_arithmetic :
    1447 = 1428 + 19 ∧
    1428 = 1422 + 6 ∧
    1422 ≤ 1795 := by decide

/-- A four-class population split admits an exact constructive loss budget. -/
theorem two_pair_merges (a b c d : Nat) :
    pairs (a + b) + pairs (c + d) =
      pairs a + pairs b + pairs c + pairs d + a*b + c*d := by
  rw [pairs_add, pairs_add]
  omega

#print axioms pairs_add
#print axioms merge_collision_gap
#print axioms phase_quotient_ledger
#print axioms nine_label_pairs
#print axioms sixty_four_pairs
#print axioms s4_stalled_eight_visit_arithmetic
#print axioms s4_stalled_four_visit_arithmetic
#print axioms s4_stalled_sixteen_visit_arithmetic
#print axioms two_pair_merges

end MathCan.PhaseGaugePairLedger
