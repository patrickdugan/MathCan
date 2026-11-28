import Init

/-!
COE-08: exact finite source-histogram and permutation-null arithmetic.

The general expected-refinement and second-moment theorems are proved in
research/compactification/OBSERVER_PERMUTATION_NULL.md; this Init-only module
checks the specified native 64-board arithmetic and histogram identities.
No source OpenAI manuscript is taken as an axiom.
-/

namespace MathCan.ObserverPermutationNull

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Original 64-board S4 target-digit histogram. -/
def targetSizes : List Nat := [10, 8, 2, 5, 8, 7, 6, 10, 8]

/-- Histogram of eight-visit positive-observation counts. -/
def counts8 : List Nat := [12, 2, 3, 1, 1, 8, 2, 8, 27]

/-- Histogram of eight-visit dihedral phase-orbit classes. -/
def bracelets8 : List Nat := [12, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8, 27]

/-- Sixteen-visit count histogram, in increasing Hamming-weight order. -/
def counts16 : List Nat := [11, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 7, 26]

/-- Sixteen-visit dihedral orbit histogram, in canonical orbit order. -/
def bracelets16 : List Nat := [11, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 26]

def squareSum (xs : List Nat) : Nat :=
  (xs.map (fun x => x * x)).sum

/-- Grounded item and distinct-target-pair totals, each in integer arithmetic. -/
theorem native_population_certificate :
    targetSizes.sum = 64 ∧
    2 * 1795 + squareSum targetSizes = 64 * 64 := by
  decide

/-- At every window, the total mass is 64. -/
theorem native_histogram_mass_certificate :
    counts8.sum = 64 ∧ bracelets8.sum = 64 ∧
    counts16.sum = 64 ∧ bracelets16.sum = 64 := by
  decide

/-- Exact original histogram-square differences. -/
theorem native_eight_moment_certificate :
    squareSum counts8 = 1020 ∧ squareSum bracelets8 = 978 ∧
    (squareSum counts8 - squareSum bracelets8) / 2 = 21 := by
  decide

theorem native_sixteen_moment_certificate :
    squareSum counts16 = 904 ∧ squareSum bracelets16 = 888 ∧
    (squareSum counts16 - squareSum bracelets16) / 2 = 8 := by
  decide

/-- Null conditional expectation is 1795/96 at T=8. The Lean cell
    checks the exact cross-multiplied integer equality. -/
theorem native_eight_expected_gain :
    1795 * (squareSum counts8 - squareSum bracelets8) * 96
      = 1795 * 64 * 63 := by
  decide

/-- Null conditional expectation is 1795/252 at T=16. -/
theorem native_sixteen_expected_gain :
    1795 * (squareSum counts16 - squareSum bracelets16) * 252
      = 1795 * 64 * 63 := by
  decide

/-- The exact second-moment-minus-mean-square rational identity at T=8,
    cross-multiplied to stay entirely in integer arithmetic. -/
theorem native_eight_variance_receipt :
    95729755 * 96 * 96 * 5809152
      = 11285015 * 272304 * 96 * 96
        + (1795 * 1795) * 272304 * 5809152 := by
  decide

/-- The corresponding T=16 arithmetic receipt. -/
theorem native_sixteen_variance_receipt :
    10908267 * 252 * 252 * 60043032
      = 46069057 * 211792 * 252 * 252
        + (1795 * 1795) * 211792 * 60043032 := by
  decide

/-- A one-sided reliability margin lower than the shuffled expectation
    can be audited without floating-point operations. -/
theorem native_eight_observation_excess :
    20 * 96 - 1795 = 125 := by
  decide

#print axioms native_population_certificate
#print axioms native_histogram_mass_certificate
#print axioms native_eight_moment_certificate
#print axioms native_sixteen_moment_certificate
#print axioms native_eight_expected_gain
#print axioms native_sixteen_expected_gain
#print axioms native_eight_variance_receipt
#print axioms native_sixteen_variance_receipt
#print axioms native_eight_observation_excess

end MathCan.ObserverPermutationNull
