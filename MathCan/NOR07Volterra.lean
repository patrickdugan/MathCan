import Init

/-!
# NOR-07T: noncommutative Volterra expansion for recurrent Jacobians

Init does not bundle the full Mathlib Semiring hierarchy. We therefore
state only the exact addition/multiplication laws needed, as explicit
hypotheses. Any (possibly noncommutative) matrix semiring satisfies them.

A_i = B_i + E_i. The exact ordered-product error propagates
with the *nominal* B_i on the left, preserving signed cancellations:

  correction (n+1) = B_n * correction n + E_n * product(A,n).

Analytic norm bounds and GRU Hessian estimates appear in the research note.
-/
namespace MathCan.NOR07Volterra

variable {R : Type}
variable [OfNat R 0] [OfNat R 1] [HAdd R R R] [HMul R R R]

/-- Time-ordered Jacobian product: newest derivative multiplies left. -/
def orderedProduct (A : Nat → R) : Nat → R
  | 0 => 1
  | n + 1 => A n * orderedProduct A n

/-- Exact Volterra correction, retaining nominal operator order. -/
def correction (B E A : Nat → R) : Nat → R
  | 0 => 0
  | n + 1 => B n * correction B E A n + E n * orderedProduct A n

/-- Noncommutative product-perturbation identity. Associativity of
multiplication and commutativity of multiplication are both unnecessary
for this recursively grouped statement. -/
theorem ordered_product_volterra
    (A B E : Nat → R)
    (hAddZero : ∀ a : R, a + 0 = a)
    (hAddMul : ∀ a b c : R, (a + b) * c = a * c + b * c)
    (hMulAdd : ∀ a b c : R, a * (b + c) = a * b + a * c)
    (hAddAssoc : ∀ a b c : R, (a + b) + c = a + (b + c))
    (h : ∀ n, A n = B n + E n) :
    ∀ n, orderedProduct A n =
      orderedProduct B n + correction B E A n := by
  intro n
  induction n with
  | zero =>
      change (1 : R) = 1 + 0
      exact (hAddZero 1).symm
  | succ n ih =>
      calc
        orderedProduct A (n + 1) =
            (B n + E n) * orderedProduct A n := by
              rw [orderedProduct, h n]
        _ = B n * orderedProduct A n + E n * orderedProduct A n :=
              hAddMul (B n) (E n) (orderedProduct A n)
        _ = B n * (orderedProduct B n + correction B E A n) +
              E n * orderedProduct A n := by
              exact congrArg
                (fun x : R => B n * x + E n * orderedProduct A n) ih
        _ = B n * orderedProduct B n +
              (B n * correction B E A n + E n * orderedProduct A n) := by
              rw [hMulAdd]
              exact hAddAssoc _ _ _
        _ = orderedProduct B (n + 1) + correction B E A (n + 1) := by
              rfl

#print axioms ordered_product_volterra

end MathCan.NOR07Volterra
