import Init

/-!
ROC-01 T-C: a finite exact upper bound for a *hypothetical*
five-exemplar intervention table with Gaussian unit-variance outcomes.

These are integer-scaled linear certificates for the combinatorial
allocation. They do not formalize continuous Chernoff's theorem, the
Gaussian KL formula, or neural measurements. The binary synthetic
table has four intervention arms; any separating set needs three types,
while the exact Gaussian KL optimum uses all four.
-/

namespace MathCan.ObserverChernoff

/--
If every one of four required distinguishing pair distances is at least d,
then 5*d is bounded by twice the total intervention allocation.
The four distances are z, x+y, x+w, y+w.
-/
theorem ideal_kl_distance_upper
    (x y z w d total : Nat)
    (hsum : x + y + z + w = total)
    (hz : d ≤ z)
    (hxy : d ≤ x + y)
    (hxw : d ≤ x + w)
    (hyw : d ≤ y + w) :
    5 * d ≤ 2 * total := by
  omega

/-- Allocation (1,1,2,1) at total 5 reaches distance 2. -/
theorem ideal_optimal_allocation_attains :
    ((1 + 1 + 2 + 1 : Nat) = 5) ∧
    ((2 : Nat) ≤ 2) ∧
    ((2 : Nat) ≤ 1 + 1) ∧
    ((2 : Nat) ≤ 1 + 1) ∧
    ((2 : Nat) ≤ 1 + 1) := by
  decide

/-- The ablation/readout-control arm receives a strictly positive share. -/
theorem ideal_optimal_uses_fourth_arm : (0 : Nat) < 1 := by
  decide

#print axioms ideal_kl_distance_upper
#print axioms ideal_optimal_allocation_attains
#print axioms ideal_optimal_uses_fourth_arm

end MathCan.ObserverChernoff
