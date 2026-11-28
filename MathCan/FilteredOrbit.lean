import Init

/-!
# NOR-02: sharpened finite-window/tail metric stitching

This module is an exact, axiom-audited Nat-metric lemma for the new
complete-Crouzeix filtered recurrence result. It assumes independently
supplied finite-window, anchor, tail-radius and tail-pair estimates.
The continuous numerical-range theorem and Lp dimension-reduction theorem
are proved at paper level in `research/nor02/FILTERED_ORBIT_CURVATURE.md`;
they are not formalized by this discrete module.

The time-indexing convention is that all i<=cutoff are known and
i>cutoff are clipped to the zero anchor. The zero anchor is index 0.
-/
namespace MathCan.FilteredOrbit

/-- A data-dependent optimized stitching budget. E is the full
window pair error, E0 is the observed-point-to-anchor error,
B is the radius bound for late points, and L is an independent
late-versus-late difference bound. -/
def optimalBudget (E E0 B L : Nat) : Nat :=
  max E (max (E0 + B) L)

/-- A measured window error plus a late-orbit radius and a separate
late-pair certificate yield a single optimized all-horizon budget.
This preserves the possibility L < 2*B obtained from a polynomial
difference in complete Crouzeix's inequality. -/
theorem refined_tail_stitch
    (cutoff E E0 B L : Nat)
    (original sketched : Nat → Nat → Nat)
    (triangle : ∀ i j k, original i k ≤ original i j + original j k)
    (symmetric : ∀ i j, original i j = original j i)
    (window : ∀ i j, i ≤ cutoff → j ≤ cutoff →
      original i j ≤ sketched i j + E ∧
      sketched i j ≤ original i j + E)
    (anchorLeft : ∀ i, i ≤ cutoff →
      original i 0 ≤ sketched i 0 + E0 ∧
      sketched i 0 ≤ original i 0 + E0)
    (anchorRight : ∀ j, j ≤ cutoff →
      original 0 j ≤ sketched 0 j + E0 ∧
      sketched 0 j ≤ original 0 j + E0)
    (tail : ∀ i, cutoff < i → original 0 i ≤ B)
    (latePair : ∀ i j, cutoff < i → cutoff < j → original i j ≤ L)
    (crossLeft : ∀ i j, i ≤ cutoff → cutoff < j →
      sketched i j = sketched i 0)
    (crossRight : ∀ i j, cutoff < i → j ≤ cutoff →
      sketched i j = sketched 0 j)
    (late : ∀ i j, cutoff < i → cutoff < j →
      sketched i j = 0) :
    ∀ i j,
      original i j ≤ sketched i j + optimalBudget E E0 B L ∧
      sketched i j ≤ original i j + optimalBudget E E0 B L := by
  have hE : E ≤ optimalBudget E E0 B L := by
    change E ≤ max E (max (E0 + B) L)
    exact Nat.le_max_left E (max (E0 + B) L)
  have hCross : E0 + B ≤ optimalBudget E E0 B L := by
    change E0 + B ≤ max E (max (E0 + B) L)
    exact Nat.le_trans (Nat.le_max_left (E0 + B) L)
      (Nat.le_max_right E (max (E0 + B) L))
  have hL : L ≤ optimalBudget E E0 B L := by
    change L ≤ max E (max (E0 + B) L)
    exact Nat.le_trans (Nat.le_max_right (E0 + B) L)
      (Nat.le_max_right E (max (E0 + B) L))
  intro i j
  by_cases hi : i ≤ cutoff
  · by_cases hj : j ≤ cutoff
    · obtain ⟨h1, h2⟩ := window i j hi hj
      constructor <;> omega
    · have hj' : cutoff < j := by omega
      have hj0 : original j 0 ≤ B := by
        rw [symmetric j 0]
        exact tail j hj'
      have h0j : original 0 j ≤ B := tail j hj'
      obtain ⟨h1, h2⟩ := anchorLeft i hi
      have ht1 := triangle i 0 j
      have ht2 := triangle i j 0
      have hs := crossLeft i j hi hj'
      constructor <;> omega
  · have hi' : cutoff < i := by omega
    by_cases hj : j ≤ cutoff
    · have h0i := tail i hi'
      have hi0 : original i 0 ≤ B := by
        rw [symmetric i 0]
        exact h0i
      obtain ⟨h1, h2⟩ := anchorRight j hj
      have ht1 := triangle i 0 j
      have ht2 := triangle 0 i j
      have hs := crossRight i j hi' hj
      constructor <;> omega
    · have hj' : cutoff < j := by omega
      have hlate := latePair i j hi' hj'
      have hs := late i j hi' hj'
      constructor <;> omega

/-- The optimized budget is bounded by the old E+2B budget whenever
the measured anchor error E0 is at most E and the late-pair bound
is at most 2B. -/
theorem optimal_budget_le_legacy (E E0 B L : Nat)
    (hAnchor : E0 ≤ E) (hLate : L ≤ 2 * B) :
    optimalBudget E E0 B L ≤ E + 2 * B := by
  unfold optimalBudget
  apply Nat.max_le_of_le_of_le
  · omega
  · apply Nat.max_le_of_le_of_le
    · omega
    · omega

/-- Two noncommuting 2-by-2 coefficient matrices appear in
C(z)=[[0,1],[z,0]], with B0*B1=diag(1,0) and
B1*B0=diag(0,1). This is a finite arithmetic certificate,
not a matrix-norm proof. -/
def B0 (i j : Nat) : Nat :=
  if i = 0 ∧ j = 1 then 1 else 0

def B1 (i j : Nat) : Nat :=
  if i = 1 ∧ j = 0 then 1 else 0

def product2 (X Y : Nat → Nat → Nat) (i j : Nat) : Nat :=
  X i 0 * Y 0 j + X i 1 * Y 1 j

theorem matrix_coefficients_noncommute :
    product2 B0 B1 0 0 = 1 ∧
    product2 B1 B0 0 0 = 0 ∧
    product2 B0 B1 1 1 = 0 ∧
    product2 B1 B0 1 1 = 1 := by
  decide

#print axioms refined_tail_stitch
#print axioms optimal_budget_le_legacy
#print axioms matrix_coefficients_noncommute

end MathCan.FilteredOrbit
