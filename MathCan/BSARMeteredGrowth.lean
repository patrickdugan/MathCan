import Init

/-!
# BSAR-06: global growth budget closes a finite-window doubling envelope

A companion to BSAR-05. The original Step 7 local chain rules allow
geometric growth across arbitrarily many windows. This module adds a
separately stated **global meter**: every strict increase consumes at
least one unit, and a single step grows by at most a factor of two.

The kernel verifies that a fixed upper bound B on total spent units
bounds the final endpoint by 2^B times its nonnegative initial value,
regardless of the number K of local windows.

This is an arithmetic conditional theorem. The model does not derive
a window cost or a global budget from Navier–Stokes dynamics.
-/

namespace MathCan.BSARMeteredGrowth

/-- Match the recursive integer doubling operator used in BSA-R Step 7. -/
def Pow2 : Nat → Int
  | 0 => 1
  | k + 1 => 2 * Pow2 k

private theorem pow2_nonneg (n : Nat) : 0 ≤ Pow2 n := by
  induction n with
  | zero => decide
  | succ n ih =>
      dsimp [Pow2]
      omega

private theorem pow2_mono_add (n cost : Nat) :
    Pow2 n ≤ Pow2 (n + cost) := by
  induction cost with
  | zero =>
      simp
  | succ cost ih =>
      rw [Nat.add_succ]
      dsimp [Pow2]
      have hn := pow2_nonneg (n + cost)
      omega

private theorem pow2_double_paid (n cost : Nat) (hpaid : 1 ≤ cost) :
    2 * Pow2 n ≤ Pow2 (n + cost) := by
  cases cost with
  | zero => omega
  | succ cost =>
      have hrec : Pow2 (n + 1) ≤ Pow2 ((n + 1) + cost) :=
        pow2_mono_add (n + 1) cost
      have heq : n + (cost + 1) = (n + 1) + cost := by omega
      rw [heq]
      have hstep : Pow2 (n + 1) = 2 * Pow2 n := rfl
      rw [hstep] at hrec
      exact hrec

private theorem pow2_monotone (a b : Nat) (h : a ≤ b) :
    Pow2 a ≤ Pow2 b := by
  have heq : a + (b - a) = b := by omega
  rw [← heq]
  exact pow2_mono_add a (b - a)

/-- A finite sequence of local steps with cumulative charged growth. -/
inductive MeteredChain : Nat → Int → Int → Nat → Prop
  | refl (d : Int) : MeteredChain 0 d d 0
  | step {k : Nat} {d0 dm dnext : Int} {used charge : Nat}
      (hprev : MeteredChain k d0 dm used)
      (hstep : dnext ≤ 2 * dm)
      (hpaid : dm < dnext → 1 ≤ charge) :
      MeteredChain (k + 1) d0 dnext (used + charge)

/-- For any horizon K, endpoint growth is bounded by total charged units. -/
theorem endpoint_le_meter (h0 : 0 ≤ d0)
    (hchain : MeteredChain K d0 dlast used) :
    dlast ≤ Pow2 used * d0 := by
  induction hchain with
  | refl d =>
      simp [Pow2]
  | @step k d0 dm dnext used charge hprev hstep hpaid ih =>
      by_cases hflat : dnext ≤ dm
      · have hmono : Pow2 used ≤ Pow2 (used + charge) :=
          pow2_mono_add used charge
        have hs := Int.mul_le_mul_of_nonneg_right hmono h0
        exact Int.le_trans hflat (Int.le_trans (ih h0) hs)
      · have hgrowth : dm < dnext := by omega
        have hunit : 1 ≤ charge := hpaid hgrowth
        have hmono : 2 * Pow2 used ≤ Pow2 (used + charge) :=
          pow2_double_paid used charge hunit
        have hs := Int.mul_le_mul_of_nonneg_right hmono h0
        have ht : 2 * dm ≤ (2 * Pow2 used) * d0 := by
          have ha := Int.mul_le_mul_of_nonneg_left (ih h0) (by omega : (0 : Int) ≤ 2)
          calc
            2 * dm ≤ 2 * (Pow2 used * d0) := ha
            _ = (2 * Pow2 used) * d0 := by rw [Int.mul_assoc]
        exact Int.le_trans hstep (Int.le_trans ht hs)

/-- One global budget cap covers all K, conditional on a charged chain. -/
theorem uniform_bound_from_global_budget
    (h0 : 0 ≤ d0)
    (hchain : MeteredChain K d0 dlast used)
    (hbudget : used ≤ B) :
    dlast ≤ Pow2 B * d0 := by
  have hstep := endpoint_le_meter (h0 := h0) hchain
  have hmono := pow2_monotone used B hbudget
  have hs := Int.mul_le_mul_of_nonneg_right hmono h0
  exact Int.le_trans hstep hs

/-- No cost implies that every allowed chain is nonincreasing. -/
theorem free_steps_cannot_increase
    (h0 : 0 ≤ d0)
    (hchain : MeteredChain K d0 dlast 0) :
    dlast ≤ d0 := by
  simpa [Pow2] using endpoint_le_meter (h0 := h0) hchain

end MathCan.BSARMeteredGrowth

#print axioms MathCan.BSARMeteredGrowth.pow2_nonneg
#print axioms MathCan.BSARMeteredGrowth.pow2_mono_add
#print axioms MathCan.BSARMeteredGrowth.pow2_double_paid
#print axioms MathCan.BSARMeteredGrowth.endpoint_le_meter
#print axioms MathCan.BSARMeteredGrowth.uniform_bound_from_global_budget
#print axioms MathCan.BSARMeteredGrowth.free_steps_cannot_increase
