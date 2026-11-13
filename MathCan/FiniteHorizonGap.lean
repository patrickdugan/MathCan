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

#print axioms epsilon_sixth_clearance
#print axioms epsilon_sixth_equiv
#print axioms full_horizon_recovers

end MathCan.FiniteHorizonGap
