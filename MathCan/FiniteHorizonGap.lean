import Init

/-!
# FHC-01: finite-horizon observation and rational-scale obstruction

Lean checks only elementary discrete lemmas used by the paper
in Compactification-Theory PR #111. The compactness, Gaussian transfer,
Lp embedding theorem and doubling Hilbert witness remain paper-level.

The natural-number clearance lemma is the exact alpha=2, D=1
instance of the robust epsilon-net transfer calculation after
cross-multiplying its positive denominator.
-/

namespace MathCan.FiniteHorizonGap

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- The exact one-sixth separation clearance in natural units. -/
theorem epsilon_sixth_clearance (delta epsilon : Nat)
    (h : 6 * epsilon ≤ delta) :
    delta + 2 * epsilon ≤ 2 * (delta - 2 * epsilon) := by
  omega

/-- The same clearance is necessary for this cross-multiplied relation. -/
theorem epsilon_sixth_equiv (delta epsilon : Nat) :
    (delta + 2 * epsilon ≤ 2 * (delta - 2 * epsilon)) ↔
      6 * epsilon ≤ delta := by
  omega

/-- Two finite states agree at horizon T if their first T symbols agree. -/
def prefixEquivalent {α : Type} (T : Nat) (xs ys : List α) : Prop :=
  xs.take T = ys.take T

/-- A horizon covering the entire state distinguishes every distinct
finite word: no extra unobserved suffix remains. -/
theorem full_horizon_recovers {α : Type} (xs ys : List α)
    (T : Nat) (hx : xs.length ≤ T) (hy : ys.length ≤ T)
    (h : prefixEquivalent T xs ys) : xs = ys := by
  dsimp [prefixEquivalent] at h
  simpa [List.take_of_length_le hx, List.take_of_length_le hy] using h

/-!
A primitive six-bit recurrence generates the observable masks used by
Compactification Theory FHC-01B. The finite orbit claims are checked
by Lean's ordinary kernel-reduced decide tactic (no native_decide).
-/

/-- Dual mask transition for h_i'=h_{i+1} (i<5),
    h_5'=h_0 XOR h_1, using six binary coordinates. -/
def nextMask (r : Nat) : Nat :=
  Nat.xor ((2 * r) % 64) (if (r / 32) % 2 = 1 then 3 else 0)

/-- The observable mask after exactly t recurrent steps. -/
def maskAt : Nat → Nat
  | 0 => 1
  | n + 1 => nextMask (maskAt n)

/-- The primitive dual recurrence returns to its first mask at 63 steps. -/
theorem mask_period_63 : maskAt 63 = 1 := by decide

/-- The first 63 observable masks have no repetitions. -/
theorem mask_orbit_nodup :
    ((List.range 63).map maskAt).Nodup := by decide

/-- None of those 63 masks vanishes. -/
theorem mask_orbit_positive :
    ∀ x ∈ (List.range 63).map maskAt, 0 < x := by decide

/-- Every observed mask belongs to the six-bit nonzero domain. -/
theorem mask_orbit_bounded :
    ∀ x ∈ (List.range 63).map maskAt, x < 64 := by decide

/-- Every possible nonzero six-bit mask appears during the first 63 visits. -/
theorem mask_orbit_complete :
    ∀ x : Fin 64, x.val ≠ 0 →
      x.val ∈ (List.range 63).map maskAt := by decide

/-- There are exactly 63 distinct nonzero observations in the orbit. -/
theorem mask_orbit_length :
    ((List.range 63).map maskAt).length = 63 := by decide

#print axioms epsilon_sixth_clearance
#print axioms epsilon_sixth_equiv
#print axioms full_horizon_recovers
#print axioms mask_period_63
#print axioms mask_orbit_nodup
#print axioms mask_orbit_positive
#print axioms mask_orbit_bounded
#print axioms mask_orbit_complete
#print axioms mask_orbit_length

end MathCan.FiniteHorizonGap
