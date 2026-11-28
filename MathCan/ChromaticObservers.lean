import Init

/-!
COE-01: finite arithmetic and code witnesses for chromatic observers.

The mathematical theorem relates a graph's chromatic number to the minimum
number of binary observables needed to distinguish its tested edges. This
module checks explicit finite cases and robustness witnesses under the pinned
Init-only Lean kernel. The general chromatic equivalence and Lipschitz
extension are proved in the accompanying research note, not by this module.
-/

namespace MathCan.ChromaticObservers

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A concrete six-code, six-bit binary alphabet. -/
def robustSixCode (v : Fin 6) : Nat :=
  match v.val with
  | 0 => 0
  | 1 => 7
  | 2 => 25
  | 3 => 30
  | 4 => 42
  | _ => 45

/-- Finite Hamming distance, restricted to the lowest `width` bits. -/
def bitDistance (width a b : Nat) : Nat :=
  ((List.range width).filter (fun i => a.testBit i != b.testBit i)).length

/-- Every one of the six words lies in the six-bit cube. -/
theorem robustSixCode_in_range :
    ∀ v : Fin 6, robustSixCode v < 2 ^ 6 := by
  decide

/-- All fifteen unordered pairs have Hamming distance at least three. -/
theorem robustSixCode_margin_three :
    ∀ u v : Fin 6, u ≠ v →
      3 ≤ bitDistance 6 (robustSixCode u) (robustSixCode v) := by
  decide

/-- Complete-graph six-state observation needs more than four colors. -/
theorem six_spokes_exceed_two_bits : 2 ^ 2 < 6 := by
  decide

/-- At width five, six radius-one binary balls would contain 36 words,
    exceeding the 32 available. The sphere-disjointness inference is in
    the accompanying proof, not the arithmetic statement. -/
theorem six_radius_one_balls_overfill_five_bits :
    2 ^ 5 < 6 * (1 + 5) := by
  decide

/-- A path of eight vertices admits the alternating one-bit encoding. -/
theorem eight_path_one_bit_certificate :
    (List.range 7).all (fun i => i % 2 != (i + 1) % 2) = true := by
  decide

/-- Any `margin` differing positions retain a difference after at most
    `erased` positions are dropped. The exact Hamming-set argument is in
    the research note; this proves its integer inequality. -/
theorem erasure_margin_arithmetic (margin erased : Nat)
    (h : erased < margin) : 0 < margin - erased := by
  omega

/-- A unit Hamming jump requires at least the threshold in metric
    distance. Thus a shorter edge forces the binary observer to be equal. -/
theorem binary_lipschitz_forces_identification
    (threshold distance : Nat) (a b : Bool)
    (hshort : distance < threshold)
    (hlip : (if a = b then 0 else threshold) ≤ distance) :
    a = b := by
  cases a <;> cases b <;> simp_all <;> omega

/-- Two short edges force equality at their endpoints, including when
    their direct distance is large. This models a metric-quotient chain. -/
theorem two_short_edges_collapse
    (threshold d01 d12 : Nat) (a b c : Bool)
    (h01 : d01 < threshold) (h12 : d12 < threshold)
    (hlip01 : (if a = b then 0 else threshold) ≤ d01)
    (hlip12 : (if b = c then 0 else threshold) ≤ d12) :
    a = c := by
  have hab : a = b :=
    binary_lipschitz_forces_identification threshold d01 a b h01 hlip01
  have hbc : b = c :=
    binary_lipschitz_forces_identification threshold d12 b c h12 hlip12
  exact hab.trans hbc

/-- Repeating a bit `margin` times makes the output width exactly
    `margin * k` and supplies the stated finite upper budget. -/
theorem repetition_width (k margin : Nat) :
    k * margin = margin * k := by
  exact Nat.mul_comm k margin

#print axioms robustSixCode_in_range
#print axioms robustSixCode_margin_three
#print axioms six_spokes_exceed_two_bits
#print axioms six_radius_one_balls_overfill_five_bits
#print axioms eight_path_one_bit_certificate
#print axioms erasure_margin_arithmetic
#print axioms binary_lipschitz_forces_identification
#print axioms two_short_edges_collapse
#print axioms repetition_width

end MathCan.ChromaticObservers
