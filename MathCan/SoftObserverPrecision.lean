import Init

/-!
COE-03: finite Lean certificates for precision–time observer capacity.

The general probabilistic O(log n) construction, volume lower bound,
precise b=Theta(log log n) necessity, and diameter-two anticode bound
are given with proofs in research/compactification/SOFT_PRECISION_DEPTH.md.
This Init-only file kernel-checks specific independently reproducible cells.
No original OpenAI manuscript is imported as an axiom.
-/

namespace MathCan.SoftObserverPrecision

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Distances are computed in numerator units, with denominator 3. -/
def softCoord (state : Fin 5) (coord : Fin 3) : Nat :=
  if state.val == 4 then 1
  else if state.val == coord.val + 1 then 3
  else 0

def absNat (a b : Nat) : Nat := (a - b) + (b - a)

def softDistanceNum (a b : Fin 5) : Nat :=
  ((List.finRange 3).map (fun j =>
    absNat (softCoord a j) (softCoord b j))).sum

/-- The five numerators represent 0,e1,e2,e3 and (1/3,1/3,1/3). -/
theorem soft_five_in_cube :
    ∀ v : Fin 5, ∀ j : Fin 3, softCoord v j ≤ 3 := by
  decide

/-- Every pair has normalized L1 distance in [1,2] with 3 heads. -/
theorem soft_five_all_pairs_separated_and_bounded :
    ∀ u v : Fin 5, u ≠ v →
      3 ≤ softDistanceNum u v ∧ softDistanceNum u v ≤ 6 := by
  decide

/-- A three-bit binary word has at most eight possibilities. -/
def hamming (width a b : Nat) : Nat :=
  ((List.range width).filter (fun j => a.testBit j != b.testBit j)).length

/-- Thresholds 0,1,2,3 on numerator values represent every possible
    coordinatewise binary threshold pattern for data in {0,1,3}.
    A threshold >3 is equivalent to t=3 if 3 were replaced by 4;
    here we use Fin 5 to cover thresholds 0,1,2,3,4 explicitly. -/
def thresholdWord (t0 t1 t2 : Fin 5) (v : Fin 5) : Nat :=
  (if t0.val ≤ softCoord v (0 : Fin 3) then 1 else 0) +
  (if t1.val ≤ softCoord v (1 : Fin 3) then 2 else 0) +
  (if t2.val ≤ softCoord v (2 : Fin 3) then 4 else 0)

/-- All coordinatewise binary threshold patterns fail at least one K5
    pair: they either collide, or their Hamming distance exceeds two.
    This is a finite statement over 5^3=125 discrete threshold choices. -/
theorem all_coordinate_thresholds_fail :
    ∀ t0 t1 t2 : Fin 5,
      ∃ u v : Fin 5, u ≠ v ∧
        (hamming 3 (thresholdWord t0 t1 t2 u) (thresholdWord t0 t1 t2 v) = 0 ∨
         3 ≤ hamming 3 (thresholdWord t0 t1 t2 u) (thresholdWord t0 t1 t2 v)) := by
  decide

/-- Five states need only four *binary* channels under Hamming cap two. -/
def binaryK5 (v : Fin 5) : Nat :=
  if v.val == 0 then 0 else 2 ^ (v.val - 1)

theorem binary_five_four_head_witness :
    ∀ u v : Fin 5, u ≠ v →
      1 ≤ hamming 4 (binaryK5 u) (binaryK5 v) ∧
      hamming 4 (binaryK5 u) (binaryK5 v) ≤ 2 := by
  decide

/-- Six states occupy 2 output bits at each of three externally clocked steps. -/
def temporalWord (v : Fin 6) (tick : Fin 3) : Nat :=
  if v.val == 2 * tick.val + 1 then 1
  else if v.val == 2 * tick.val + 2 then 2
  else 0

def transcriptDistance (a b : Fin 6) : Nat :=
  ((List.finRange 3).map (fun tick =>
    hamming 2 (temporalWord a tick) (temporalWord b tick))).sum

theorem six_states_two_heads_three_ticks :
    ∀ u v : Fin 6, u ≠ v →
      1 ≤ transcriptDistance u v ∧ transcriptDistance u v ≤ 2 := by
  decide

/-- The independent 1,024-state Python certificate has extreme raw Hamming
    distances 91 and 168 at scale 12/1023. The Lean theorem checks the
    resulting rational inequalities, rather than the 523,776 raw pairs. -/
theorem pinned_grid_extrema_within_margin_and_budget :
    1023 ≤ 91 * 12 ∧ 168 * 12 ≤ 2 * 1023 := by
  decide

/-- Coordinatewise scalar extension costs at most k*a; the finite grid
    witness has k*a = 3072/1023 < 4. -/
theorem pinned_grid_extension_constant_below_four :
    256 * 12 < 4 * 1023 := by
  decide

#print axioms soft_five_in_cube
#print axioms soft_five_all_pairs_separated_and_bounded
#print axioms all_coordinate_thresholds_fail
#print axioms binary_five_four_head_witness
#print axioms six_states_two_heads_three_ticks
#print axioms pinned_grid_extrema_within_margin_and_budget
#print axioms pinned_grid_extension_constant_below_four

end MathCan.SoftObserverPrecision
