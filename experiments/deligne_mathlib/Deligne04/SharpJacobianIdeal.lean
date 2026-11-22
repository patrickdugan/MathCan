import Deligne04.GlobalJacobianIdeal
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

/-!
# DEL-14: exact equivalence between the discriminant and Jacobian unit ideal

DEL-13 proved: c-a*b != 0 -> (F,F_X,F_Y) = (1).
The converse follows by evaluating at the explicit singular point
(X,Y)=(-b,-a) when c=a*b: all three generators vanish there.
Evaluation is a true ring homomorphism, so the entire Jacobian ideal
lies in its kernel and cannot contain 1.

This closes the algebraic if-and-only-if statement for the conic
family over any field, including characteristic two. It is a
global polynomial ideal statement. A scheme-level Jacobian
criterion is required for the geometric smoothness equivalence.
-/

namespace Deligne14

/-- The true conic polynomial vanishes at the critical point
(-b,-a) exactly on the discriminant. -/
theorem conic_eval_at_critical_of_delta_zero
    {K : Type*} [Field K] (a b c : K)
    (hc : c = a * b) :
    MvPolynomial.eval (Deligne12.conicPoint (-b) (-a))
      (Deligne12.conicPolynomial K a b c) = 0 := by
  rw [Deligne12.eval_conicPolynomial, hc]
  ring

/-- The true x partial derivative vanishes at the critical point. -/
theorem conic_pderiv_x_eval_at_critical
    {K : Type*} [Field K] (a b c : K) :
    MvPolynomial.eval (Deligne12.conicPoint (-b) (-a))
      (MvPolynomial.pderiv false (Deligne12.conicPolynomial K a b c)) = 0 := by
  rw [Deligne12.eval_pderiv_conic_x]
  ring

/-- The true y partial derivative also vanishes there. -/
theorem conic_pderiv_y_eval_at_critical
    {K : Type*} [Field K] (a b c : K) :
    MvPolynomial.eval (Deligne12.conicPoint (-b) (-a))
      (MvPolynomial.pderiv true (Deligne12.conicPolynomial K a b c)) = 0 := by
  rw [Deligne12.eval_pderiv_conic_y]
  ring

/-- If c=a*b, evaluation at (-b,-a) kills every generator of
the conic Jacobian ideal. The whole ideal is contained in the
kernel of a ring homomorphism to the nontrivial field K. -/
theorem jacobian_ideal_le_singular_eval_ker
    {K : Type*} [Field K] (a b c : K)
    (hc : c = a * b) :
    Deligne13.conicJacobianIdeal K a b c ≤
      RingHom.ker
        (MvPolynomial.eval (Deligne12.conicPoint (-b) (-a))) := by
  let F := Deligne12.conicPolynomial K a b c
  let Fx := MvPolynomial.pderiv false F
  let Fy := MvPolynomial.pderiv true F
  change Ideal.span ({F, Fx, Fy} : Set (MvPolynomial Bool K)) ≤
    RingHom.ker (MvPolynomial.eval (Deligne12.conicPoint (-b) (-a)))
  apply Ideal.span_le.mpr
  intro p hp
  have hg : p = F ∨ p = Fx ∨ p = Fy := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp
  rcases hg with h | h | h
  · rw [h]
    exact RingHom.mem_ker.mpr
      (conic_eval_at_critical_of_delta_zero a b c hc)
  · rw [h]
    exact RingHom.mem_ker.mpr
      (conic_pderiv_x_eval_at_critical a b c)
  · rw [h]
    exact RingHom.mem_ker.mpr
      (conic_pderiv_y_eval_at_critical a b c)

/-- On the singular discriminant, the actual polynomial Jacobian
ideal is proper. Evaluation at (-b,-a) witnesses its properness
without an appeal to Hilbert's Nullstellensatz. -/
theorem conic_jacobian_ideal_ne_top_of_delta_zero
    {K : Type*} [Field K] (a b c : K)
    (hc : c = a * b) :
    Deligne13.conicJacobianIdeal K a b c ≠ ⊤ := by
  intro htop
  have hle := jacobian_ideal_le_singular_eval_ker a b c hc
  have h1 : (1 : MvPolynomial Bool K) ∈
      Deligne13.conicJacobianIdeal K a b c := by
    rw [htop]
    exact Submodule.mem_top
  have hker :
      (1 : MvPolynomial Bool K) ∈
        RingHom.ker
          (MvPolynomial.eval (Deligne12.conicPoint (-b) (-a))) :=
    hle h1
  have hzero :
      MvPolynomial.eval (Deligne12.conicPoint (-b) (-a))
        (1 : MvPolynomial Bool K) = 0 :=
    RingHom.mem_ker.mp hker
  have h10 : (1 : K) = 0 := by
    simpa using hzero
  exact one_ne_zero h10

/-- The sharp algebraic discriminant criterion:
the Jacobian ideal (F,F_X,F_Y) is the entire polynomial ring
if and only if the conic discriminant c-a*b is nonzero. -/
theorem conic_jacobian_ideal_top_iff
    {K : Type*} [Field K] (a b c : K) :
    Deligne13.conicJacobianIdeal K a b c = ⊤ ↔
      c ≠ a * b := by
  constructor
  · intro htop
    by_contra hdelta
    have hc : c = a * b := of_not_ne hdelta
    exact (conic_jacobian_ideal_ne_top_of_delta_zero
      a b c hc) htop
  · exact Deligne13.conic_jacobian_ideal_eq_top a b c

/-- The complementary proper-ideal criterion is exactly
the discriminant equation c=a*b. -/
theorem conic_jacobian_ideal_proper_iff
    {K : Type*} [Field K] (a b c : K) :
    Deligne13.conicJacobianIdeal K a b c ≠ ⊤ ↔
      c = a * b := by
  rw [ne_eq, conic_jacobian_ideal_top_iff]
  exact not_ne_iff

#print axioms conic_eval_at_critical_of_delta_zero
#print axioms conic_pderiv_x_eval_at_critical
#print axioms conic_pderiv_y_eval_at_critical
#print axioms jacobian_ideal_le_singular_eval_ker
#print axioms conic_jacobian_ideal_ne_top_of_delta_zero
#print axioms conic_jacobian_ideal_top_iff
#print axioms conic_jacobian_ideal_proper_iff

end Deligne14
