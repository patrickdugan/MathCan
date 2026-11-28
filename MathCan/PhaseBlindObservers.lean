import Init

/-!
# COE-06: phase-blind constant-count recurrent observer certificates

The companion research note proves the cyclic-orbit distance and one-deletion
resource theorems. Here Lean checks the twenty-one concrete fourteen-tick
register words and exact arithmetic at the two largest subcritical widths.

The finite exhaustive resource ledger for all T <= 13 is verified separately
by the standard-library Python oracle. Thus the global minimality theorem is
proved in the manuscript, while the present file formalizes a finite witness
and the critical integer budget implications; it does not encode every
enumerated resource class in Lean.
-/

namespace MathCan.PhaseBlindObservers

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- Twenty-one length-14, weight-six binary orbit representatives. -/
def word (label : Fin 21) : Nat :=
  match label.val with
  | 0 => 207
  | 1 => 243
  | 2 => 311
  | 3 => 473
  | 4 => 543
  | 5 => 629
  | 6 => 697
  | 7 => 811
  | 8 => 851
  | 9 => 903
  | 10 => 1133
  | 11 => 1175
  | 12 => 1337
  | 13 => 1351
  | 14 => 1419
  | 15 => 1445
  | 16 => 1587
  | 17 => 1677
  | 18 => 1865
  | 19 => 2451
  | _ => 2709

/-- Fixed, time-independent transition on fourteen-bit registers. -/
def rotate14 (state : Nat) : Nat :=
  state / 2 + (state % 2) * 8192

/-- Apply the same transition for each iteration. -/
def rotateN : Nat → Nat → Nat
  | 0, state => state
  | n + 1, state => rotate14 (rotateN n state)

/-- The single shared readout is the low bit of the current register. -/
def readBit (state : Nat) : Bool := state.testBit 0

/-- Finite, exact Hamming statistics. -/
def bitWeight14 (state : Nat) : Nat :=
  ((List.range 14).filter (fun bit => state.testBit bit)).length

def bitDistance14 (left right : Nat) : Nat :=
  ((List.range 14).filter (fun bit => left.testBit bit != right.testBit bit)).length

/-- Every word fits fourteen bits and contains exactly six set bits. -/
theorem code_fits_and_constant_weight :
    ∀ label : Fin 21, word label < 2 ^ 14 ∧ bitWeight14 (word label) = 6 := by
  decide

/-- The time-independent transition leaves every representative in the cube. -/
theorem rotation_fits :
    ∀ label : Fin 21, rotate14 (word label) < 2 ^ 14 := by
  decide

/-- Pairwise min-distance certificate, chunked to control kernel reduction cost. -/
private theorem margin_low :
    ∀ i j : Fin 21, i.val < 7 → i ≠ j →
      ∀ phase : Fin 14,
        4 ≤ bitDistance14 (word i) (rotateN phase.val (word j)) := by
  decide

private theorem margin_mid :
    ∀ i j : Fin 21, 7 ≤ i.val → i.val < 14 → i ≠ j →
      ∀ phase : Fin 14,
        4 ≤ bitDistance14 (word i) (rotateN phase.val (word j)) := by
  decide

private theorem margin_high :
    ∀ i j : Fin 21, 14 ≤ i.val → i ≠ j →
      ∀ phase : Fin 14,
        4 ≤ bitDistance14 (word i) (rotateN phase.val (word j)) := by
  decide

/-- Any two different labels remain distance >=4 after an arbitrary
    unknown cyclic shift of either transcript. One-bit flips are therefore
    correctable by nearest-orbit decoding. -/
theorem cyclic_orbit_margin_four
    (i j : Fin 21) (distinct : i ≠ j) (phase : Fin 14) :
    4 ≤ bitDistance14 (word i) (rotateN phase.val (word j)) := by
  by_cases hlow : i.val < 7
  · exact margin_low i j hlow distinct phase
  by_cases hmid : i.val < 14
  · have hlo : 7 ≤ i.val := by omega
    exact margin_mid i j hlo hmid distinct phase
  · have hhi : 14 ≤ i.val := by omega
    exact margin_high i j hhi distinct phase

/-- At T=13,w=6, six candidate necklaces cost five deletion-orbits each;
    all remaining candidates cost six. There are 99 resources total. -/
theorem width13_resource_budget
    (special regular : Nat)
    (hs : special ≤ 6)
    (hbudget : 5 * special + 6 * regular ≤ 99) :
    special + regular ≤ 17 := by
  omega

/-- At T=12,w=6, exact candidate cost multiplicities are
    (cost,count)=(1,1),(2,1),(3,3),(5,4),(6,71).
    The 66 deletion-orbits allow at most fourteen labels. -/
theorem width12_resource_budget
    (one two three five six : Nat)
    (h1 : one ≤ 1) (h2 : two ≤ 1)
    (h3 : three ≤ 3) (h5 : five ≤ 4)
    (hbudget : one + 2 * two + 3 * three + 5 * five + 6 * six ≤ 66) :
    one + two + three + five + six ≤ 14 := by
  omega

/-- Full constant-count transcript has the same activity histogram. -/
theorem any_two_labels_same_count (i j : Fin 21) :
    bitWeight14 (word i) = bitWeight14 (word j) := by
  calc
    bitWeight14 (word i) = 6 := (code_fits_and_constant_weight i).2
    _ = bitWeight14 (word j) := ((code_fits_and_constant_weight j).2).symm

#print axioms code_fits_and_constant_weight
#print axioms rotation_fits
#print axioms cyclic_orbit_margin_four
#print axioms width13_resource_budget
#print axioms width12_resource_budget
#print axioms any_two_labels_same_count

end MathCan.PhaseBlindObservers
