import Init

/-!
# SPC-01: exact four-phase Fourier pilot certificates

Finite field F_5 has a fourth root of unity 2: 1,2,4,3.
The four-phase Fourier synthesis is represented by natural-number
arithmetic modulo 5, so the results use only Lean's trusted `decide`.

This certifies the finite d=4, k=1 two-pilot uniqueness case, the
sharp three-pilot collision for k=2, and character orthogonality.
It does not formalize the arbitrary complex-field Vandermonde theorem
stated in research/spectral_aliasing/SPC-01.md.
-/

namespace MathCan.SpectralAliasing

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The powers of 2 in F_5, a primitive fourth root of unity. -/
def omega4 (e : Nat) : Nat :=
  if e % 4 == 0 then 1
  else if e % 4 == 1 then 2
  else if e % 4 == 2 then 4
  else 3

/-- Four-point Fourier synthesis, omitting a common invertible factor 1/4. -/
def synth4 (coeff : Fin 4 → Nat) (phase : Fin 4) : Nat :=
  (((List.finRange 4).map
    (fun f => coeff f * omega4 (phase.val * f.val))).sum) % 5

/-- A source with one unknown frequency and nonzero coefficient. -/
def singleton4 (amp : Fin 5) (frequency : Fin 4) : Fin 4 → Nat :=
  fun f => if f == frequency then amp.val else 0

/-- Every nontrivial character has sum zero over the four phases. -/
theorem four_phase_character_orthogonality :
    ∀ j : Fin 4,
      (((List.finRange 4).map
        (fun s => omega4 (s.val * j.val))).sum) % 5 =
          if j.val == 0 then 4 else 0 := by
  decide

/-- The four roots 1,2,4,3 are pairwise different modulo 5. -/
theorem fourth_roots_distinct :
    ∀ f g : Fin 4, omega4 f.val = omega4 g.val → f = g := by
  decide

/-- Two consecutive phases identify one unknown Fourier frequency:
phase zero identifies the nonzero amplitude, and phase one identifies
which of the four fourth roots multiplies that amplitude. -/
theorem two_pilots_identify_one_sparse :
    ∀ a b : Fin 5, ∀ i j : Fin 4,
      a.val ≠ 0 →
      synth4 (singleton4 a i) 0 = synth4 (singleton4 b j) 0 →
      synth4 (singleton4 a i) 1 = synth4 (singleton4 b j) 1 →
      i = j := by
  decide

/-- One phase cannot distinguish two frequencies with the same amplitude. -/
theorem one_pilot_collision :
    synth4 (singleton4 1 0) 0 = synth4 (singleton4 1 1) 0 := by
  decide

/-- First two Fourier coefficients, a two-sparsu source. -/
def coeffA (f : Fin 4) : Nat :=
  if f.val == 0 then 1 else if f.val == 1 then 2 else 0

/-- Last two Fourier coefficients, a different two-sparsu source. -/
def coeffB (f : Fin 4) : Nat :=
  if f.val == 2 then 1 else if f.val == 3 then 2 else 0

/-- Two different two-sparsu sources share the first three pilots. -/
theorem three_pilots_collide_two_sparse :
    ∀ s : Fin 4, s.val < 3 → synth4 coeffA s = synth4 coeffB s := by
  decide

/-- The fourth pilot separates the two sources. -/
theorem fourth_pilot_separates :
    synth4 coeffA 3 ≠ synth4 coeffB 3 := by
  decide

/-- A two-sparsu four-frequency source whose phase-zero observation vanishes. -/
def hiddenTwo (f : Fin 4) : Nat :=
  if f.val == 0 then 1 else if f.val == 1 then 4 else 0

/-- A single phase may completely miss the active two-sparsu source. -/
theorem one_pilot_hides_two_sparse :
    synth4 hiddenTwo 0 = 0 ∧ synth4 hiddenTwo 1 ≠ 0 := by
  decide

/-- Finite four-coordinate amplitude input, with each entry reduced mod five. -/
def coeff4 (a b c d : Fin 5) (f : Fin 4) : Nat :=
  if f.val == 0 then a.val
  else if f.val == 1 then b.val
  else if f.val == 2 then c.val
  else d.val

/-- Number of occupied Fourier frequencies. -/
def support4 (coeff : Fin 4 → Nat) : Nat :=
  ((List.finRange 4).filter (fun f => coeff f % 5 != 0)).length

/-- Exhaustive F_5 certificate of sharp two-phase detectability for
all 625 amplitude vectors with at most two active frequencies. -/
theorem two_pilots_detect_two_sparse :
    ∀ a b c d : Fin 5,
      support4 (coeff4 a b c d) ≤ 2 →
      synth4 (coeff4 a b c d) 0 = 0 →
      synth4 (coeff4 a b c d) 1 = 0 →
      a.val = 0 ∧ b.val = 0 ∧ c.val = 0 ∧ d.val = 0 := by
  decide

#print axioms four_phase_character_orthogonality
#print axioms fourth_roots_distinct
#print axioms two_pilots_identify_one_sparse
#print axioms one_pilot_collision
#print axioms three_pilots_collide_two_sparse
#print axioms fourth_pilot_separates
#print axioms one_pilot_hides_two_sparse
#print axioms two_pilots_detect_two_sparse

end MathCan.SpectralAliasing
