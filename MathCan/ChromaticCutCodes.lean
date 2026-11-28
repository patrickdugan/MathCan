import Init

/-!
COE-02: exact finite certificates for integer-cut observers.

This module checks K5's five-state/three-bit antipodal obstruction,
the sharp four-bit code at ell_1 distance budget two, and balanced-cut
identities underlying the fractional relaxation optimum 5/3.

The general integer cut theorem, anticode bound and unbounded integrality
gap have written proofs in CHROMATIC_CUT_CAPACITY.md. This Init-only
module establishes selected finite examples, not those general theorems.
-/

namespace MathCan.ChromaticCutCodes

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def hamming (width a b : Nat) : Nat :=
  ((List.range width).filter (fun i => a.testBit i != b.testBit i)).length

/-- Five pairwise separated words realizing the L=2 equilateral K5 budget. -/
def k5Witness (v : Fin 5) : Nat :=
  match v.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | _ => 8

theorem k5_witness_within_four_bits :
    ∀ v : Fin 5, k5Witness v < 2 ^ 4 := by
  decide

theorem k5_witness_pairwise_margin_and_cap :
    ∀ u v : Fin 5, u ≠ v →
      1 ≤ hamming 4 (k5Witness u) (k5Witness v) ∧
      hamming 4 (k5Witness u) (k5Witness v) ≤ 2 := by
  decide

/-- Three-bit antipodal pairs, namely (0,7),(1,6),(2,5),(3,4). -/
theorem three_cube_antipodes_distance_three :
    ∀ v : Fin 4, hamming 3 v.val (7 - v.val) = 3 := by
  decide

/-- Any five selected words from the 3-cube contain an antipodal pair.
    The mask ranges over all 256 subsets of the eight three-bit words. -/
theorem five_three_bit_words_force_antipodal_pair :
    ∀ subset : Fin 256,
      5 ≤ ((List.range 8).filter (fun w => subset.val.testBit w)).length →
        ((List.range 4).any (fun i =>
          subset.val.testBit i && subset.val.testBit (7 - i))) = true := by
  decide

/-- A balanced cut on five states contains 2 or 3 states and is
    canonically oriented to exclude state zero. -/
def balancedCut5 (mask : Nat) : Bool :=
  let count := ((List.range 5).filter (fun i => mask.testBit i)).length
  (mask.testBit 0 == false) && (count == 2 || count == 3)

def splits5 (mask u v : Nat) : Bool :=
  mask.testBit u != mask.testBit v

def balanceSplitCount (u v : Nat) : Nat :=
  ((List.range 32).filter (fun mask =>
    balancedCut5 mask && splits5 mask u v)).length

def cutPairCount5 (mask : Nat) : Nat :=
  ((List.range 5).flatMap (fun u =>
    (List.range 5).filter (fun v =>
      decide (u < v) && splits5 mask u v))).length

theorem ten_balanced_cuts_on_five_points :
    ((List.range 32).filter balancedCut5).length = 10 := by
  decide

theorem each_pair_crosses_six_balanced_cuts :
    ∀ u v : Fin 5, u ≠ v → balanceSplitCount u.val v.val = 6 := by
  decide

theorem every_five_state_cut_crosses_at_most_six_pairs :
    ∀ mask : Fin 32, cutPairCount5 mask.val ≤ 6 := by
  decide

theorem balanced_cuts_cross_exactly_six_pairs :
    ∀ mask : Fin 32, balancedCut5 mask.val = true →
      cutPairCount5 mask.val = 6 := by
  decide

/-- Cross-multiplied exact equality 10*(1/6) = 5/3. -/
theorem k5_fractional_mass_cross_multiplication : 10 * 3 = 5 * 6 := by
  decide

/-- The sharp K5 integer / fractional ratio equals 12/5. -/
theorem k5_integrality_ratio_cross_multiplication : 4 * 3 = 12 := by
  decide

#print axioms k5_witness_within_four_bits
#print axioms k5_witness_pairwise_margin_and_cap
#print axioms three_cube_antipodes_distance_three
#print axioms five_three_bit_words_force_antipodal_pair
#print axioms ten_balanced_cuts_on_five_points
#print axioms each_pair_crosses_six_balanced_cuts
#print axioms every_five_state_cut_crosses_at_most_six_pairs
#print axioms balanced_cuts_cross_exactly_six_pairs
#print axioms k5_fractional_mass_cross_multiplication
#print axioms k5_integrality_ratio_cross_multiplication

end MathCan.ChromaticCutCodes
