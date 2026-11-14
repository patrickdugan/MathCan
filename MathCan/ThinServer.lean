import Init

/-!
TKS-01 finite metric/cut witness, from OpenAI Math #110 × #174.

The general randomized k-server and strong-thin-tree theorems are imported
research claims. This module kernel-checks the complete K8 path example,
its optimal cut coefficient, an explicit one-edge failure, the average
pair-distance arithmetic and the elementary transfer inequality.

The Python companion proves the general n formula and independently
enumerates every cut through sixteen vertices.
-/

namespace MathCan.ThinServer

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Number of labeled vertices on the specified side of a cut of K8. -/
def vertexCount8 (mask : Nat) : Nat :=
  ((List.range 8).filter (fun i => mask.testBit i)).length

/-- Original unit complete-graph cut capacity: a(8-a). -/
def completeCut8 (mask : Nat) : Nat :=
  vertexCount8 mask * (8 - vertexCount8 mask)

/-- Number of unit path edges crossing a labeled cut. -/
def pathCrossing8 (mask : Nat) : Nat :=
  ((List.range 7).filter (fun i =>
    (mask.testBit i) != (mask.testBit (i + 1)))).length

/-- All 254 nontrivial cuts of K8 satisfy
  |δ_T(S)| <= (49/16)/7 * |δ_G(S)| = 7/16 |δ_G(S)|.

Both rational denominators are cleared: 16*7=112.
The finite oracle checks exactly each possible vertex subset. -/
theorem every_eight_vertex_cut_thin :
    ∀ mask : Fin 256,
      mask.val ≠ 0 → mask.val ≠ 255 →
      112 * pathCrossing8 mask.val ≤ 49 * completeCut8 mask.val := by
  decide

/-- Alternating side {0,2,4,6} attains the exact coefficient 49/16. -/
theorem alternating_cut_attains_bound :
    pathCrossing8 85 = 7 ∧ completeCut8 85 = 16 ∧
      112 * pathCrossing8 85 = 49 * completeCut8 85 := by
  decide

/-- The selected thinness parameter lies below the universal constant 4. -/
theorem finite_strong_thinness_below_four :
    (49 : Nat) < 4 * 16 := by
  decide

/-- The sum of tree path distances over all 28 unordered
distinct vertex pairs is 84, hence the average is 3. -/
def allPairDistances8 : Nat :=
  ((List.range 8).flatMap (fun i =>
    ((List.range 8).filter (fun j => i < j)).map (fun j => j - i))).sum

theorem sum_unordered_path_distances8 :
    allPairDistances8 = 84 := by
  decide

theorem mean_tree_distance8 :
    (28 : Nat) * 3 = allPairDistances8 := by
  decide

/-- Two initial servers at positions 0 and 1; a new request for 7.
Original K8 cost one; the nearest server along P8 is six edges away. -/
theorem one_request_service_gap8 :
    min (7 - 0) (7 - 1) = 6 ∧ (1 : Nat) < 6 := by
  decide

/-- Removing the path edge (3,4) eliminates the only tree edge across
the cut {0,1,2,3}; the original K8 cut still contains 15 edges. -/
def pathCutAfterOneFault8 (mask fault : Nat) : Nat :=
  ((List.range 7).filter (fun i =>
    i != fault && ((mask.testBit i) != (mask.testBit (i+1))))).length

theorem thin_path_single_fault_disconnects :
    pathCrossing8 15 = 1 ∧ pathCutAfterOneFault8 15 3 = 0 ∧
      completeCut8 15 = 16 ∧ completeCut8 15 - 1 = 15 := by
  decide

/-- A general algebraic transfer lemma: the same legal move stream
has original cost at most surrogate cost; compare offline optima
under the two metrics and apply any surrogate competitive bound. -/
theorem surrogate_cost_transfer
    (costG costT competitive optT optG stretch additive : Nat)
    (hmovement : costG ≤ costT)
    (hcompetitive : costT ≤ competitive * optT + additive)
    (hopt : optT ≤ stretch * optG) :
    costG ≤ competitive * stretch * optG + additive := by
  calc
    costG ≤ costT := hmovement
    _ ≤ competitive * optT + additive := hcompetitive
    _ ≤ competitive * (stretch * optG) + additive :=
      Nat.add_le_add_right (Nat.mul_le_mul_left competitive hopt) additive
    _ = competitive * stretch * optG + additive := by
      simp [Nat.mul_assoc]

#print axioms every_eight_vertex_cut_thin
#print axioms alternating_cut_attains_bound
#print axioms finite_strong_thinness_below_four
#print axioms sum_unordered_path_distances8
#print axioms mean_tree_distance8
#print axioms one_request_service_gap8
#print axioms thin_path_single_fault_disconnects
#print axioms surrogate_cost_transfer

end MathCan.ThinServer
