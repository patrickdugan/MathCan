import MathCan.BSARChainAudit
import MathCan.BSARMeteredGrowth

/-!
# BSAR-07: a cumulative nonnegative window integral is sufficient for uniformity

The published BSA-R Step7 local conditions imply that a single window grows
its endpoint by at most a factor of two. Adding a *cumulative* and
*nonnegative integer-valued* ledger for the local Im terms connects those
conditions to the independently checked BSAR-06 metered growth theorem.

The decisive extra premises are:
* every Im is an exact Nat cost (and therefore cannot be negative),
* every window's Im is included in the cumulative ledger,
* the global ledger has a uniform bound B independent of K.

This module makes no claim that a real PDE integral is an integer cost or
that the required global bound follows from Navier-Stokes energy estimates.
-/

namespace MathCan.BSARWindowBudget

/-- An augmented copy of BSA-R Step7's inductive window rules that
    also accumulates every nonnegative integer Im as a Nat budget. -/
inductive WindowChain (M : Int) : Nat → Int → Int → Nat → Prop
  | refl (d : Int) : WindowChain M 0 d d 0
  | step {k : Nat} {d0 dm dnext : Int} {used Im : Nat}
      (hprev : WindowChain M k d0 dm used)
      (hdnext_nn : 0 ≤ dnext)
      (hwin_ode : M * (dnext - dm) ≤ (Im : Int) * dnext)
      (hwin_half_budget : 2 * (Im : Int) ≤ M) :
      WindowChain M (k + 1) d0 dnext (used + Im)

/-- Source-aligned: forgetting the ledger recovers BSA-R's original
    finite `LerayDoublingChain` proposition, exactly as written. -/
theorem forget_ledger
    (hchain : WindowChain M K d0 dfinal spent) :
    BSARChainAudit.LerayDoublingChain M K d0 dfinal := by
  induction hchain with
  | refl d => exact BSARChainAudit.LerayDoublingChain.refl d
  | @step k d0 dm dnext used Im hprev hnn hode hhalf ih =>
      exact BSARChainAudit.LerayDoublingChain.step ih hnn hode hhalf

/-- The published half-budget arithmetic gives the local doubling bound. -/
private theorem local_doubling
    {M dm dnext : Int} {Im : Nat}
    (hM : 0 < M) (hnn : 0 ≤ dnext)
    (hode : M * (dnext - dm) ≤ (Im : Int) * dnext)
    (hhalf : 2 * (Im : Int) ≤ M) :
    dnext ≤ 2 * dm := by
  have h2ode : 2 * (M * (dnext - dm)) ≤ (2 * (Im : Int)) * dnext := by
    have hm := Int.mul_le_mul_of_nonneg_left hode (by omega : (0 : Int) ≤ 2)
    rw [← Int.mul_assoc 2 (Im : Int) dnext] at hm
    exact hm
  have hhalfmul : (2 * (Im : Int)) * dnext ≤ M * dnext :=
    Int.mul_le_mul_of_nonneg_right hhalf hnn
  have hle : 2 * (M * (dnext - dm)) ≤ M * dnext :=
    Int.le_trans h2ode hhalfmul
  have hrw : 2 * (M * (dnext - dm)) = M * (2 * dnext - 2 * dm) := by
    rw [Int.mul_sub M dnext dm, Int.mul_sub 2 (M * dnext) (M * dm),
        Int.mul_sub M (2 * dnext) (2 * dm)]
    have s1 : 2 * (M * dnext) = M * (2 * dnext) := by
      rw [← Int.mul_assoc 2 M dnext, Int.mul_comm 2 M, Int.mul_assoc M 2 dnext]
    have s2 : 2 * (M * dm) = M * (2 * dm) := by
      rw [← Int.mul_assoc 2 M dm, Int.mul_comm 2 M, Int.mul_assoc M 2 dm]
    rw [s1, s2]
  rw [hrw] at hle
  by_cases hd : dnext ≤ 2 * dm
  · exact hd
  · have hgt : dnext < 2 * dnext - 2 * dm := by omega
    have hMgt := Int.mul_lt_mul_of_pos_left hgt hM
    omega

/-- A strictly increasing window consumes at least one integer unit.
    This implication depends on the Nat-valued, nonnegative Im charge. -/
private theorem strict_growth_has_positive_cost
    {M dm dnext : Int} {Im : Nat}
    (hM : 0 < M)
    (hode : M * (dnext - dm) ≤ (Im : Int) * dnext)
    (hgrowth : dm < dnext) : 1 ≤ Im := by
  by_contra h
  have hzero : Im = 0 := by omega
  subst Im
  simp only [Nat.cast_zero, zero_mul] at hode
  have hpos : 0 < M * (dnext - dm) :=
    Int.mul_pos hM (by omega)
  omega

/-- Every well-accounted BSA-R window chain admits the BSAR-06
    metered certificate with the SAME cumulative cost, and same horizon. -/
theorem to_metered_chain
    (hM : 0 < M)
    (hchain : WindowChain M K d0 dfinal spent) :
    BSARMeteredGrowth.MeteredChain K d0 dfinal spent := by
  induction hchain with
  | refl d => exact BSARMeteredGrowth.MeteredChain.refl d
  | @step k d0 dm dnext used Im hprev hnn hode hhalf ih =>
      have hdouble : dnext ≤ 2 * dm := local_doubling hM hnn hode hhalf
      have hpaid : dm < dnext → 1 ≤ Im :=
        strict_growth_has_positive_cost hM hode
      exact BSARMeteredGrowth.MeteredChain.step ih hdouble hpaid

/-- Explicit finite aggregate Im control gives a K-INDEPENDENT endpoint cap.
    This is conditional arithmetic, with a separately supplied global budget. -/
theorem uniform_bound_from_integer_window_budget
    (hM : 0 < M)
    (h0 : 0 ≤ d0)
    (hchain : WindowChain M K d0 dfinal spent)
    (hbudget : spent ≤ B) :
    dfinal ≤ BSARMeteredGrowth.Pow2 B * d0 := by
  exact BSARMeteredGrowth.uniform_bound_from_global_budget
    h0 (to_metered_chain hM hchain) hbudget

end MathCan.BSARWindowBudget

#print axioms MathCan.BSARWindowBudget.forget_ledger
#print axioms MathCan.BSARWindowBudget.to_metered_chain
#print axioms MathCan.BSARWindowBudget.uniform_bound_from_integer_window_budget
