import Init

/-!
# SPC-03J: finite quadratic endpoint-Jacobian secant certificate

For F(x)=a*x^2+b*x modulo 7, the exact Taylor remainder relative to
F'(y) is -a*(y-x)^2. The result is verified exhaustively for all
7^4 coefficient / endpoint choices by Lean's kernel-checkable `decide`.
The Hilbert-space C^2 secant theorem in SPC-03J.md is paper mathematics;
this file certifies a non-affine finite-field specialization only.
-/

namespace MathCan.JacobianSecant

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def quadratic7 (a b x : Nat) : Nat := (a*x*x + b*x) % 7

def difference7 (y x : Nat) : Nat := (y+7-x)%7

/-- Finite-field specialization of
    F(y)-F(x) = F'(y)(y-x) - a(y-x)^2, F(x)=a*x^2+b*x.
    All arguments range over F_7 and reductions are canonical Nats. -/
theorem quadratic_endpoint_remainder7 :
    ∀ a b x y : Fin 7,
      (quadratic7 a.val b.val y.val + 7 - quadratic7 a.val b.val x.val) % 7 =
        (((2*a.val*y.val + b.val) * difference7 y.val x.val + 7 -
           (a.val * difference7 y.val x.val * difference7 y.val x.val) % 7) % 7) := by
  decide

/-- The exact polynomial specializes to affine shifts when a=0. -/
theorem affine_endpoint_remainder7 :
    ∀ b x y : Fin 7,
      (quadratic7 0 b y.val + 7 - quadratic7 0 b x.val) % 7 =
        (b.val * difference7 y.val x.val) % 7 := by
  decide

#print axioms quadratic_endpoint_remainder7
#print axioms affine_endpoint_remainder7

end MathCan.JacobianSecant
