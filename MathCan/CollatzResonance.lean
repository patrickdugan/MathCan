import Init

/-!
# COL-01: actual odd-map descent and invariant obstructions

This file uses Lean's kernel and Init. The map removes every factor of two
after its selected odd branch. Reciprocity, the all-moduli classification,
and branch-count lattice completeness have separate written proofs.
-/
namespace MathCan.CollatzResonance

def stripTwos (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 0 then stripTwos (n / 2)
  else n
termination_by n
decreasing_by omega

theorem stripTwos_le (n : Nat) : stripTwos n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [stripTwos]
    split
    · omega
    · split
      · have hn : n / 2 < n := by omega
        have hi := ih (n / 2) hn
        omega
      · omega

theorem stripTwos_pos (n : Nat) (hn : 0 < n) : 0 < stripTwos n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [stripTwos]
    split
    · omega
    · split
      · apply ih (n / 2) (by omega) (by omega)
      · omega

theorem stripTwos_odd (n : Nat) (hn : 0 < n) : stripTwos n % 2 = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [stripTwos]
    split
    · omega
    · split
      · apply ih (n / 2) (by omega) (by omega)
      · omega

theorem stripTwos_quarter (n : Nat) (hn : n % 4 = 0) :
    4 * stripTwos n ≤ n := by
  by_cases hz : n = 0
  · subst n
    simp [stripTwos]
  have he : n % 2 = 0 := by omega
  have hh : n / 2 ≠ 0 := by omega
  have heh : n / 2 % 2 = 0 := by omega
  rw [stripTwos, ite_eq_right hz, ite_eq_left he]
  rw [stripTwos, ite_eq_right hh, ite_eq_left heh]
  have h := stripTwos_le (n / 2 / 2)
  omega

def numerator (d n : Nat) : Nat := if n % 4 = 1 then 3*n+d else n+d
def oddNext (d n : Nat) : Nat := stripTwos (numerator d n)

theorem numerator_divisible_four (d n : Nat)
    (hd : d % 4 = 1) (hn : n % 2 = 1) : numerator d n % 4 = 0 := by
  unfold numerator
  split <;> omega

theorem oddNext_pos (d n : Nat) (hd : d % 4 = 1) : 0 < oddNext d n := by
  apply stripTwos_pos
  unfold numerator
  split <;> omega

theorem oddNext_odd (d n : Nat) (hd : d % 4 = 1) : oddNext d n % 2 = 1 := by
  apply stripTwos_odd
  unfold numerator
  split <;> omega

theorem oddNext_bound (d n : Nat) (hd : d % 4 = 1) (hn : n % 2 = 1) :
    4 * oddNext d n ≤ 3*n+d := by
  have h := stripTwos_quarter (numerator d n) (numerator_divisible_four d n hd hn)
  have hnum : numerator d n ≤ 3*n+d := by
    unfold numerator
    split <;> omega
  exact Nat.le_trans h hnum

theorem odd_core_closed (d n : Nat) (hd : d % 4 = 1)
    (hn : n % 2 = 1) (hcore : n ≤ d) : oddNext d n ≤ d := by
  have h := oddNext_bound d n hd hn
  omega

theorem odd_descent_above_core (d n : Nat) (hd : d % 4 = 1)
    (hn : n % 2 = 1) (habove : d < n) : oddNext d n < n := by
  have h := oddNext_bound d n hd hn
  omega

def iterate {S : Type} (step : S → S) : Nat → S → S
  | 0, x => x
  | k+1, x => iterate step k (step x)

theorem eventually_in_odd_core (d n : Nat) (hd : d % 4 = 1) (hn : n % 2 = 1) :
    ∃ k, iterate (oddNext d) k n ≤ d := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hcore : n ≤ d
    · exact ⟨0, hcore⟩
    · have hlt := odd_descent_above_core d n hd hn (by omega)
      obtain ⟨k, hk⟩ := ih (oddNext d n) hlt (oddNext_odd d n hd)
      exact ⟨k+1, hk⟩

theorem invariant_iterate {S L : Type} (step : S → S) (label : S → L)
    (conserved : ∀ x, label (step x) = label x) (k : Nat) (x : S) :
    label (iterate step k x) = label x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => exact (ih (step x)).trans (conserved x)

theorem distinct_labels_prevent_meeting {S L : Type} (step : S → S) (label : S → L)
    (conserved : ∀ x, label (step x) = label x) (x y : S)
    (different : label x ≠ label y) (j k : Nat) :
    iterate step j x ≠ iterate step k y := by
  intro h
  have e := congrArg label h
  rw [invariant_iterate step label conserved, invariant_iterate step label conserved] at e
  exact different e

theorem aliased_targets_prevent_decoder {S L B : Type}
    (label : S → L) (target : S → B) (x y : S)
    (alias : label x = label y) (different : target x ≠ target y) :
    ¬ ∃ decode : L → B, ∀ z, decode (label z) = target z := by
  intro ⟨decode, correct⟩
  apply different
  calc
    target x = decode (label x) := (correct x).symm
    _ = decode (label y) := congrArg decode alias
    _ = target y := correct y

theorem short_window_residue_injective (m x y : Nat)
    (hx : x < m) (hy : y < m) (same : x % m = y % m) : x = y := by
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using same

theorem d13_cycle_one : oddNext 13 1 = 1 := by simp [oddNext, numerator, stripTwos]
theorem d13_cycle_five : oddNext 13 5 = 7 ∧ oddNext 13 7 = 5 := by
  simp [oddNext, numerator, stripTwos]
theorem d13_modular_alias : (1 * 2^9) % 13 = 5 := by decide
theorem reference_lattice_determinant : 1522*1308 + 2024*1354 = 2*2365636 := by decide

#print axioms stripTwos_le
#print axioms stripTwos_pos
#print axioms stripTwos_odd
#print axioms stripTwos_quarter
#print axioms numerator_divisible_four
#print axioms oddNext_pos
#print axioms oddNext_odd
#print axioms oddNext_bound
#print axioms odd_core_closed
#print axioms odd_descent_above_core
#print axioms eventually_in_odd_core
#print axioms invariant_iterate
#print axioms distinct_labels_prevent_meeting
#print axioms aliased_targets_prevent_decoder
#print axioms short_window_residue_injective
#print axioms d13_cycle_one
#print axioms d13_cycle_five
#print axioms d13_modular_alias
#print axioms reference_lattice_determinant

end MathCan.CollatzResonance
