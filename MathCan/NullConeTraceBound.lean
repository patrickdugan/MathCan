import Std

/-!
# A finite-sum capacity bound

This module proves the natural-number version of a trace lower-bound argument.
Each `w i` is an integer weight after choosing a common scale. The proof uses
only finite partial sums. It does not construct a Hilbert space, an operator
trace, a spectral projection, or a gravitational clock.

The analytic bridge to the real-valued Hilbert-space theorem is stated in the
accompanying audit note. The theorem names below describe only this module's
finite-sum scope.
-/

namespace MathCan.NullConeTraceBound

/-- Sum the first `n` scaled weights. -/
def partialWeight (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => partialWeight w n + w n

/-- A lower bound on every weight gives a linear lower bound on each sum. -/
theorem partialWeight_lower_bound
    (w : Nat → Nat) (m : Nat) (hw : ∀ i, m ≤ w i) :
    ∀ n, n * m ≤ partialWeight w n := by
  intro n
  induction n with
  | zero =>
      simp [partialWeight]
  | succ n ih =>
      calc
        (n + 1) * m = n * m + m := Nat.succ_mul n m
        _ ≤ partialWeight w n + w n := Nat.add_le_add ih (hw n)
        _ = partialWeight w (n + 1) := rfl

/-- If each scaled weight is at least one, a total budget bounds the count. -/
theorem count_le_budget
    (w : Nat → Nat) (m n Z : Nat)
    (hm : 1 ≤ m) (hw : ∀ i, m ≤ w i)
    (hZ : partialWeight w n ≤ Z) :
    n ≤ Z := by
  calc
    n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * m := Nat.mul_le_mul_left n hm
    _ ≤ partialWeight w n := partialWeight_lower_bound w m hw n
    _ ≤ Z := hZ

/-- An infinite list of positive scaled weights has no finite total budget. -/
theorem no_uniform_partialWeight_bound
    (w : Nat → Nat) (m Z : Nat)
    (hm : 1 ≤ m) (hw : ∀ i, m ≤ w i)
    (hZ : ∀ n, partialWeight w n ≤ Z) :
    False := by
  have hcount : Z + 1 ≤ Z :=
    count_le_budget w m (Z + 1) Z hm hw (hZ (Z + 1))
  exact Nat.not_succ_le_self Z hcount

/-- Existential form of the same obstruction. -/
theorem no_finite_budget
    (w : Nat → Nat) (m : Nat)
    (hm : 1 ≤ m) (hw : ∀ i, m ≤ w i) :
    ¬ ∃ Z, ∀ n, partialWeight w n ≤ Z := by
  intro h
  cases h with
  | intro Z hZ =>
      exact no_uniform_partialWeight_bound w m Z hm hw hZ

#print axioms partialWeight_lower_bound
#print axioms count_le_budget
#print axioms no_uniform_partialWeight_bound
#print axioms no_finite_budget

end MathCan.NullConeTraceBound
