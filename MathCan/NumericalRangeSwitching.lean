import Init

/-!
# NRF-01: a finite arithmetic skeleton for switched disturbance bounds

This checks a recursive comparison lemma for repeated weighted errors.
Complex norm and Crouzeix estimates are kept in the paper-level proof.
Natural rates are placeholders, not fractional contractivity coefficients.
-/

namespace MathCan.NumericalRangeSwitching

/-- Error budget under constant natural amplification and disturbance. -/
def affineBudget (gain noise : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => gain * affineBudget gain noise n + noise

/-- A recursively bounded finite error trace lies below the budget. -/
theorem recursive_error_bound (gain noise : Nat) (err : Nat → Nat)
    (h0 : err 0 = 0)
    (hstep : ∀ n, err (n + 1) ≤ gain * err n + noise)
    (n : Nat) : err n ≤ affineBudget gain noise n := by
  induction n with
  | zero => simp [h0, affineBudget]
  | succ k ih =>
      calc
        err (k + 1) ≤ gain * err k + noise := hstep k
        _ ≤ gain * affineBudget gain noise k + noise :=
          Nat.add_le_add_right (Nat.mul_le_mul_left gain ih) noise
        _ = affineBudget gain noise (k + 1) := rfl

/-- With zero disturbance, the finite error budget vanishes. -/
theorem zero_disturbance_budget (gain n : Nat) :
    affineBudget gain 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [affineBudget, ih]

#print axioms recursive_error_bound
#print axioms zero_disturbance_budget

end MathCan.NumericalRangeSwitching
