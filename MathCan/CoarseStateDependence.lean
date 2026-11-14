import Init

/-!
KSR-01C finite algebra bridge. The probability theorems in
Compactification-Theory THEORY_C.md remain separately scoped.

For two equally likely full parent states with child-probability
numerators a,b over a common denominator k, the conditional sibling
covariance has numerator (a-b)^2 over 4*k^2. The identity below
checks the cancellation for every integer a,b. It does not introduce
conditional expectation or a real-probability measure into Init.
-/
namespace MathCan.CoarseStateDependence

/-- Four times the variance of a two-point scalar is a squared difference. -/
theorem two_parent_covariance_numerator (a b : Int) :
    2 * (a * a + b * b) - (a + b) * (a + b) =
      (a - b) * (a - b) := by
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul]
  have h : b * a = a * b := Int.mul_comm b a
  omega

/-- Two deterministic children copy the same hidden Boolean parent. -/
def child (h : Bool) : Bool := h

def bothFalseCount : Nat :=
  ([false, true].filter fun h => (!child h) && (!child h)).length

def singleFalseCount : Nat :=
  ([false, true].filter fun h => !child h).length

/-- The joint mass is 1/2, while multiplying the two marginals gives 1/4. -/
theorem joint_exceeds_product_marginal :
    2 * bothFalseCount > singleFalseCount * singleFalseCount := by
  decide

/-- b=4, lambda=1/2, fully shared sibling innovations:
    normalized variance grows by three at each level. -/
def sharedCriticalMoment : Nat → Nat
  | 0 => 1
  | n + 1 => sharedCriticalMoment n + 3

theorem shared_critical_linear_growth (n : Nat) :
    sharedCriticalMoment n = 1 + 3 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [sharedCriticalMoment]
      omega

theorem one_level_shared_moment : sharedCriticalMoment 1 = 4 := by
  decide

/-- The incorrectly imported IID bound 5/7 exceeds true MAP 2/3.
    Cross multiplication uses the positive denominators 7 and 3. -/
theorem iid_claim_exceeds_true_shared_accuracy :
    (5 : Nat) * 3 > 2 * 7 := by
  decide

/-- Corrected floor 1/2 is below true MAP 2/3 in the same finite example. -/
theorem corrected_floor_below_true_shared_accuracy :
    (1 : Nat) * 3 ≤ 2 * 2 := by
  decide

#print axioms two_parent_covariance_numerator
#print axioms joint_exceeds_product_marginal
#print axioms shared_critical_linear_growth
#print axioms one_level_shared_moment
#print axioms iid_claim_exceeds_true_shared_accuracy
#print axioms corrected_floor_below_true_shared_accuracy

end MathCan.CoarseStateDependence
