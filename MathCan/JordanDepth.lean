import Init

/-!
NRF-07: arithmetic core of unipotent Jordan depth growth.
The full real-valued Pareto law has a written proof and exact Fraction tests.
This module establishes the nilpotent shear recurrence in Nat algebra.
-/

namespace MathCan.JordanDepth

/-- Multiplication of upper triangular matrices [[a,b],[0,a]]. -/
def upperMul (x y : Nat × Nat) : Nat × Nat :=
  (x.1 * y.1, x.1 * y.2 + x.2 * y.1)

/-- Natural-number powers of [[1,b],[0,1]]. -/
def upperPower (b : Nat) : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 => upperMul (upperPower b n) (1, b)

/-- The nilpotent off-diagonal component grows linearly in depth. -/
theorem upperPower_closed (b n : Nat) :
    upperPower b n = (1, n * b) := by
  induction n with
  | zero => simp [upperPower]
  | succ n ih =>
    simp [upperPower, upperMul, ih, Nat.succ_mul, Nat.add_comm]

/-- Doubling depth doubles the unipotent off-diagonal component. -/
theorem double_shear (b n : Nat) :
    (upperPower b (2 * n)).2 = 2 * (upperPower b n).2 := by
  rw [upperPower_closed, upperPower_closed]
  simp only [Prod.snd]
  ac_rfl

/-- Squared depth doubles twice, giving fourfold leakage penalty. -/
theorem double_depth_square (n : Nat) :
    (2 * n) * (2 * n) = 4 * (n * n) := by
  calc
    (2 * n) * (2 * n) = (2 * 2) * (n * n) := by ac_rfl
    _ = 4 * (n * n) := rfl

#print axioms upperPower_closed
#print axioms double_shear
#print axioms double_depth_square

end MathCan.JordanDepth
