import Init

/-!
# DMB-01: finite deletion deck witness and terminal decoding obstruction

A small kernel-checked bridge for the deletion-memory campaign in
Compactification Theory PR #112. These lemmas do not formalize the
OpenAI #122 superpolynomial trace lower bound or the OpenAI #140
Gaussian streaming theorem.

Words are represented by bit values at positions 0..3; the test words
0110 and 1001 correspond to natural numbers 6 and 9. A deletion mask
retains bit positions where its bit is true. All 16 masks are enumerated.
-/

namespace MathCan.DeletionMemory

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- A deterministic terminal decoder cannot correctly decode two
different inputs if their terminal compressed states collide. -/
theorem correct_decoder_separates
    {Source Memory : Type}
    (encode : Source → Memory) (decode : Memory → Source)
    {x y : Source}
    (hx : decode (encode x) = x)
    (hy : decode (encode y) = y)
    (hxy : x ≠ y) : encode x ≠ encode y := by
  intro h
  apply hxy
  calc
    x = decode (encode x) := hx.symm
    _ = decode (encode y) := congrArg decode h
    _ = y := hy

/-- Exact ordinary deletion trace of a four-position word.
The mask is hidden; only the resulting ordered bits remain. -/
def trace4 (source mask : Nat) : List Bool :=
  ((List.range 4).filter fun i => mask.testBit i).map fun i => source.testBit i

/-- Number of deletion masks leading to the observed trace. -/
def deckCount4 (source : Nat) (trace : List Bool) : Nat :=
  ((List.range 16).filter fun mask => trace4 source mask == trace).length

/-- The seven distinct binary strings of length at most two. -/
def shortTraces : List (List Bool) :=
  [[], [false], [true], [false,false], [false,true],
   [true,false], [true,true]]

/-- The eight possible three-bit traces. -/
def threeTraces : List (List Bool) :=
  [[false,false,false], [false,false,true],
   [false,true,false], [false,true,true],
   [true,false,false], [true,false,true],
   [true,true,false], [true,true,true]]

/-- The two four-bit strings have equal deletion-deck multiplicities
for EVERY trace of length at most two. -/
theorem short_decks_identical :
    ∀ t ∈ shortTraces, deckCount4 6 t = deckCount4 9 t := by
  decide

/-- All length-three trace supports of the two sources are disjoint. -/
theorem three_decks_disjoint :
    ∀ t ∈ threeTraces, deckCount4 6 t = 0 ∨ deckCount4 9 t = 0 := by
  decide

/-- There are four masks retaining exactly three out of four bits. -/
theorem three_deck_mass_count_left :
    ((threeTraces.map (deckCount4 6)).sum) = 4 := by
  decide

theorem three_deck_mass_count_right :
    ((threeTraces.map (deckCount4 9)).sum) = 4 := by
  decide

/-- There is one four-bit unredacted trace per source. -/
theorem full_trace_count_left :
    deckCount4 6 [false,true,true,false] = 1 := by decide

theorem full_trace_count_right :
    deckCount4 9 [true,false,false,true] = 1 := by decide

#print axioms correct_decoder_separates
#print axioms short_decks_identical
#print axioms three_decks_disjoint
#print axioms three_deck_mass_count_left
#print axioms three_deck_mass_count_right
#print axioms full_trace_count_left
#print axioms full_trace_count_right

end MathCan.DeletionMemory
