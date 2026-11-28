import Init

/-!
NRF-04: discrete cross-multiplied shadow of the Jordan risk/leakage Pareto identity.

For rational unit directions with Pythagorean numerators a,b and common
denominator d, the analytic frontier has error b²/d² and leakage
|coupling| a²/d². These Nat lemmas check the cross-multiplied
arithmetic and the positive-coupling perfect-task obstruction.

The squared real norm, stochastic linear risk, and tanh Jacobian
claims remain in the paper-level proof.
-/

namespace MathCan.ObservablePareto

theorem pythagorean_frontier
    (a b denom gain : Nat)
    (hunit : a*a + b*b = denom*denom) :
    gain*(a*a) + gain*(b*b) = gain*(denom*denom) := by
  calc
    gain*(a*a) + gain*(b*b) =
        gain*((a*a) + (b*b)) := (Nat.mul_add gain (a*a) (b*b)).symm
    _ = gain*(denom*denom) := congrArg (fun x : Nat => gain*x) hunit

theorem perfect_task_forces_positive_leakage
    (a b denom gain : Nat)
    (hunit : a*a + b*b = denom*denom)
    (hdenom : 0 < denom)
    (hgain : 0 < gain)
    (hperfect : b = 0) :
    0 < gain * (a*a) := by
  have ha : a*a = denom*denom := by
    simpa [hperfect] using hunit
  rw [ha]
  exact Nat.mul_pos hgain (Nat.mul_pos hdenom hdenom)

#print axioms pythagorean_frontier
#print axioms perfect_task_forces_positive_leakage

end MathCan.ObservablePareto
