import Init

/-!
COE-07R: a four-level observer quotient for ordered histories, cyclic
necklaces, dihedral bracelets and counts. These lemmas check arithmetic
under stated collision premises; the full combinatorial orbit theorem
appears in the accompanying MathCan manuscript.
-/
namespace MathCan.DihedralPhaseGauge

set_option maxHeartbeats 1000000

/-- Nested collision classes yield an exact three-part loss ledger. -/
theorem dihedral_collision_ledger
    (eligible orderedCollision cyclicCollision dihedralCollision countCollision : Nat)
    (h₁ : orderedCollision ≤ cyclicCollision)
    (h₂ : cyclicCollision ≤ dihedralCollision)
    (h₃ : dihedralCollision ≤ countCollision)
    (h₄ : countCollision ≤ eligible) :
    eligible - orderedCollision =
      (eligible - countCollision) +
      (countCollision - dihedralCollision) +
      (dihedralCollision - cyclicCollision) +
      (cyclicCollision - orderedCollision) := by
  omega

/-- In a merge of two label classes, cross-pairs split into same-label
    and different-label parts, with no probabilistic assumptions. -/
theorem two_label_cross_pairs (a₀ a₁ b₀ b₁ : Nat) :
    (a₀ + a₁) * (b₀ + b₁) =
      (a₀*b₀ + a₁*b₁) + (a₀*b₁ + a₁*b₀) := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- The best single label for a merged class cannot outperform the two
    separate classwise-majority decoders. -/
theorem majority_cannot_improve_after_merge (a₀ a₁ b₀ b₁ : Nat) :
    max (a₀ + b₀) (a₁ + b₁) ≤ max a₀ a₁ + max b₀ b₁ := by
  omega

/-- Numeric Burnside checksum, conditional on exact orbit enumerations. -/
theorem eight_visit_weight_four_burnside_arithmetic :
    10 + 6 = 2 * 8 := by decide

/-- Exact native trace arithmetic in the 64-board stalled stratum. -/
theorem native_s4_eight_visit_ledger :
    1414 = 1389 + 25 ∧
    1389 = 1389 + 0 ∧
    1389 = 1369 + 20 ∧
    1414 ≤ 1795 := by decide

/-- Sixteen visits retain only six dihedral-over-count distinctions. -/
theorem native_s4_sixteen_visit_ledger :
    1447 = 1428 + 19 ∧
    1428 = 1422 + 6 ∧
    1447 ≤ 1795 := by decide

#print axioms dihedral_collision_ledger
#print axioms two_label_cross_pairs
#print axioms majority_cannot_improve_after_merge
#print axioms eight_visit_weight_four_burnside_arithmetic
#print axioms native_s4_eight_visit_ledger
#print axioms native_s4_sixteen_visit_ledger

end MathCan.DihedralPhaseGauge
