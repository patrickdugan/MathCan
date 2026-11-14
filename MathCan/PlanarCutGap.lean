import Init

/-!
# PLC-01: finite planar K2,3 SDP and L1 cut certificates

This Lean/Init companion verifies the *finite rational arithmetic*
of Control-Harness PLC-01, pairing OpenAI Math #089 and #117.

Distances d3 are the candidate SDP squared distances multiplied by 3.
embedding9 is the explicitly cut-generated L1 distance multiplied by 9.
All 30 nontrivial cuts are enumerated exactly in the Lean kernel.

The generic negative-type/Gram PSD theorem, GL convex symmetrization,
large-n integrality-gap source result, and general planar L1 embedding
theorem remain in separate mathematical arguments and external sources.
-/

namespace MathCan.PlanarCutGap

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

def sideA (u : Fin 5) : Bool := u.val < 2

def cutMember (mask : Nat) (u : Fin 5) : Bool := mask.testBit u.val

def separates (mask : Nat) (u v : Fin 5) : Bool :=
  cutMember mask u != cutMember mask v

def supplyEdge (u v : Fin 5) : Bool :=
  sideA u != sideA v

def supplyCut (mask : Nat) : Nat :=
  ((List.finRange 5).flatMap (fun u =>
    ((List.finRange 5).filter (fun v => u.val < v.val)).map
      (fun v => if supplyEdge u v && separates mask u v then 1 else 0))).sum

def cutSize (mask : Nat) : Nat :=
  ((List.finRange 5).filter (fun u => cutMember mask u)).length

def demandCut (mask : Nat) : Nat :=
  cutSize mask * (5 - cutSize mask)

/-- The actual uniform sparsest cut ratio is at least 1/2 for all
nontrivial cuts. A singleton in the three-vertex side attains it. -/
theorem every_nontrivial_cut_ratio_ge_half :
    ∀ mask : Fin 32, mask.val != 0 → mask.val != 31 →
      demandCut mask.val ≤ 2 * supplyCut mask.val := by
  decide

theorem singleton_B_cut_attains_half :
    supplyCut 4 = 2 ∧ demandCut 4 = 4 := by
  decide

/-- All distances are scaled by 3 to use integer arithmetic:
d01=4/3, d23=d24=d34=2, and all six cross distances=1. -/
def sdpD3 (u v : Fin 5) : Nat :=
  if u == v then 0
  else if u.val < 2 && v.val < 2 then 4
  else if 2 ≤ u.val && 2 ≤ v.val then 6
  else 3

def graphD3 (u v : Fin 5) : Nat :=
  if u == v then 0
  else if (u.val < 2 && v.val < 2) ||
          (2 ≤ u.val && 2 ≤ v.val) then 6
  else 3

theorem scaled_sdp_triangle :
    ∀ u v w : Fin 5,
      sdpD3 u w ≤ sdpD3 u v + sdpD3 v w := by
  decide

/-- Integer Gram entries equal 3 times the exact rational Gram. -/
def gram3 (u v : Fin 5) : Int :=
  if u.val < 2 && v.val < 2 then
    if u == v then 1 else -1
  else if 2 ≤ u.val && 2 ≤ v.val then
    if u == v then 2 else -1
  else 0

theorem scaled_sdp_is_squared_gram_distance :
    ∀ u v : Fin 5,
      (sdpD3 u v : Int) =
        gram3 u u + gram3 v v - 2 * gram3 u v := by
  decide

/-- An exact finite kernel check of the zero-sum negative-type face. -/
def zeroSumWeight (i : Fin 5) : Int :=
  if i.val < 2 then 3 else -2

def hyperWeight (i : Fin 5) : Int :=
  if i.val < 2 then -1 else 1

def weightedPairSum (w : Fin 5 → Int)
    (dist : Fin 5 → Fin 5 → Nat) : Int :=
  ((List.finRange 5).flatMap (fun i =>
    ((List.finRange 5).filter (fun j => i.val < j.val)).map
      (fun j => w i * w j * (dist i j : Int)))).sum

theorem sdp_negative_type_face :
    weightedPairSum zeroSumWeight sdpD3 = 0 := by
  decide

/-- Graph geodesic has half-negative-type form 6, so scaled by
three its violating integer form is +18. -/
theorem planar_graph_geodesic_fails_negative_type :
    weightedPairSum zeroSumWeight graphD3 = 18 := by
  decide

/-- Hypermetric scores of the SDP and graph geodesic are positive.
A positive score violates an exact L1 isometry condition. -/
theorem five_point_hypermetric_violations :
    weightedPairSum hyperWeight sdpD3 = 4 ∧
    weightedPairSum hyperWeight graphD3 = 6 := by
  decide

def weightedCutScore (mask : Nat) : Int :=
  ((List.finRange 5).flatMap (fun i =>
    ((List.finRange 5).filter (fun j => i.val < j.val)).map
      (fun j => if separates mask i j then
        hyperWeight i * hyperWeight j else 0))).sum

/-- Every cut satisfies the five-point integer hypermetric inequality. -/
theorem every_cut_hypermetric_nonpositive :
    ∀ mask : Fin 32, weightedCutScore mask.val ≤ 0 := by
  decide

/-- Numerators of weights with common denominator nine:
six A/B doubletons at 2/9, three B singletons at 5/9. -/
def cutWeight9 (mask : Nat) : Nat :=
  if mask ∈ [5,9,17,6,10,18] then 2
  else if mask ∈ [4,8,16] then 5 else 0

def l1Numerator9 (u v : Fin 5) : Nat :=
  ((List.range 32).map (fun mask =>
    if separates mask u v then cutWeight9 mask else 0)).sum

/-- d3/3 <= L1_9/9 <= (11/9)*d3/3,
after clearing all denominators by 9. -/
theorem nine_cut_embedding_bounds :
    ∀ u v : Fin 5,
      3 * sdpD3 u v ≤ l1Numerator9 u v ∧
      3 * l1Numerator9 u v ≤ 11 * sdpD3 u v := by
  decide

theorem l1_support_cuts_are_all_optimal :
    ∀ mask : Fin 32,
      0 < cutWeight9 mask.val →
      demandCut mask.val = 2 * supplyCut mask.val := by
  decide

theorem nine_cut_weight_numerators :
    ((List.range 32).map cutWeight9).sum = 27 := by
  decide

theorem normalized_SDP_and_cut_gap_arithmetic :
    (9 : Nat) * 40 = 20 * 18 ∧
    10 * 9 = 20 * 9 / 2 := by
  decide

/-- Explicit gap: true objective 1/2 exceeds the relaxation 9/20. -/
theorem relaxed_score_strictly_below_best_cut :
    (9 : Nat) * 2 < 20 := by
  decide

/-- Rational threshold tau=19/40 accepts SDP 9/20 and
rejects every true cut of sparsity >=1/2. -/
theorem relaxation_admission_is_unsound :
    (9 : Nat) * 40 < 19 * 20 ∧
    19 * 2 < 40 := by
  decide

#print axioms every_nontrivial_cut_ratio_ge_half
#print axioms singleton_B_cut_attains_half
#print axioms scaled_sdp_triangle
#print axioms scaled_sdp_is_squared_gram_distance
#print axioms sdp_negative_type_face
#print axioms planar_graph_geodesic_fails_negative_type
#print axioms five_point_hypermetric_violations
#print axioms every_cut_hypermetric_nonpositive
#print axioms nine_cut_embedding_bounds
#print axioms l1_support_cuts_are_all_optimal
#print axioms nine_cut_weight_numerators
#print axioms normalized_SDP_and_cut_gap_arithmetic
#print axioms relaxed_score_strictly_below_best_cut
#print axioms relaxation_admission_is_unsound

end MathCan.PlanarCutGap
