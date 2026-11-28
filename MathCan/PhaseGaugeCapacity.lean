import Init

/-!
# COE-05: finite witnesses for phase-gauge observer capacity

The associated MathCan research note proves the general constant-count,
error-correcting and orbit-capacity statements. This Init-only file checks
the explicit 14-code affine F2^3 witness and finite arithmetic instances.
It does not claim a Lean proof of the general packing or Burnside theorems.
-/

namespace MathCan.PhaseGaugeCapacity

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

/-- Binary dot product on three bits. -/
def dotParity3 (a x : Nat) : Bool :=
  ((a.testBit 0 && x.testBit 0) != (a.testBit 1 && x.testBit 1)) !=
    (a.testBit 2 && x.testBit 2)

/-- Characteristic number of the affine plane a·x=side in F2^3. -/
def affinePlaneWord (a side : Nat) : Nat :=
  ((List.range 8).map (fun x =>
    if dotParity3 a x == (side == 1) then 2 ^ x else 0)).sum

/-- The fourteen affine hyperplane words indexed by seven nonzero normals. -/
def phaseWord (label : Fin 14) : Nat :=
  affinePlaneWord (label.val / 2 + 1) (label.val % 2)

/-- Number of set bits among the lowest width coordinates. -/
def bitWeight (width word : Nat) : Nat :=
  ((List.range width).filter (fun i => word.testBit i)).length

/-- Hamming distance on fixed-length binary words. -/
def bitDistance (width left right : Nat) : Nat :=
  ((List.range width).filter (fun i => left.testBit i != right.testBit i)).length

/-- This exact table independently checks the affine normal/side generator. -/
theorem affine_plane_table :
    ((List.finRange 14).map phaseWord) =
      [85, 170, 51, 204, 153, 102, 15, 240, 165, 90, 195, 60, 105, 150] := by
  decide

/-- The phase register has fourteen distinct 8-bit words. -/
theorem phase_code_in_range :
    ∀ label : Fin 14, phaseWord label < 2 ^ 8 := by
  decide

/-- Count-only observation always reads four positive phases. -/
theorem phase_code_constant_weight :
    ∀ label : Fin 14, bitWeight 8 (phaseWord label) = 4 := by
  decide

/-- Distinct labels are distance at least four, allowing one bit flip. -/
theorem phase_code_margin_four :
    ∀ left right : Fin 14, left ≠ right →
      4 ≤ bitDistance 8 (phaseWord left) (phaseWord right) := by
  decide

/-- One fixed recurrent shift, independent of the label and visit. -/
def rotateRight8 (word : Nat) : Nat :=
  word / 2 + (word % 2) * 128

/-- Recurrent register after t visits. -/
def stateAt (word : Nat) : Nat → Nat
  | 0 => word
  | t + 1 => rotateRight8 (stateAt word t)

/-- One fixed bit-zero readout applied at every visit. -/
def temporalBit (label : Fin 14) (visit : Nat) : Bool :=
  (stateAt (phaseWord label) visit).testBit 0

/-- The eight ordered reads reconstruct the original codeword exactly. -/
theorem tied_shift_recovers_code :
    ∀ label : Fin 14,
      ((List.range 8).map (temporalBit label)) =
        ((List.range 8).map (fun i => (phaseWord label).testBit i)) := by
  decide

/-- Four triples per support, 56 triples in the full 8-point set. -/
theorem eight_phase_triple_packing_saturated : 14 * 4 = 56 := by
  decide

/-- Integer obstruction for a seven-phase, fourteen-label constant-count code.
    The general subset-packing argument is in the research note. -/
theorem seven_phase_packing_arithmetic :
    14 * 2 > 7 ∧ 14 * 3 > 21 ∧ 14 * 4 > 35 := by
  decide

/-- A four-positive-visit count is identical for all fourteen labels. -/
theorem histogram_cannot_separate (left right : Fin 14) :
    bitWeight 8 (phaseWord left) = bitWeight 8 (phaseWord right) := by
  calc
    bitWeight 8 (phaseWord left) = 4 := phase_code_constant_weight left
    _ = bitWeight 8 (phaseWord right) := (phase_code_constant_weight right).symm

#print axioms affine_plane_table
#print axioms phase_code_in_range
#print axioms phase_code_constant_weight
#print axioms phase_code_margin_four
#print axioms tied_shift_recovers_code
#print axioms eight_phase_triple_packing_saturated
#print axioms seven_phase_packing_arithmetic
#print axioms histogram_cannot_separate

end MathCan.PhaseGaugeCapacity
