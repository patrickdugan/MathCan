import Deligne04.EmbeddedLineBadLocus
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

/-!
# DEL-17: degree-three Bertini bad-locus certificate for an actual U²

Let U be the smooth parabola y=x² in A². On U² the fixed
bilinear path coordinate B=x₀*x₁ is part of the graph embedding.

The restricted fixed-coefficient hyperplane equation is the genuine
polynomial G=α*x₀²+x₀*x₁+β*x₁²+p*x₀+q*x₁+c in K[x₀,x₁].

Using actual MvPolynomial.pderiv, we prove the universal Bézout
identity

  (4αβ-1)G - α G_y² - β G_x² + G_x G_y
    = C((4αβ-1)c - αq² - βp² + pq).

It is valid in every commutative ring, including characteristic two.
The eliminant is a nonzero degree-at-most-three polynomial in the
hyperplane parameters over EVERY field. Every singular section
parameter therefore lies in its zero locus.

This is a fully explicit embedded-product example, not a claim that
the same formula describes an arbitrary embedded U^k. Katz's
weak-Lefschetz open remains a separate geometric input.
-/

namespace Deligne17

/-- The actual restriction of the fixed-bilinear hyperplane on
the embedded product of two affine parabolas. -/
noncomputable def parabolaSection
    (K : Type*) [CommRing K] (alpha beta p q c : K) :
    MvPolynomial Bool K :=
  MvPolynomial.C alpha * MvPolynomial.X false * MvPolynomial.X false +
    MvPolynomial.X false * MvPolynomial.X true +
    MvPolynomial.C beta * MvPolynomial.X true * MvPolynomial.X true +
    MvPolynomial.C p * MvPolynomial.X false +
    MvPolynomial.C q * MvPolynomial.X true +
    MvPolynomial.C c

/-- The formal x partial derivative, evaluated in Mathlib's
actual multivariate polynomial ring. -/
theorem pderiv_parabola_x
    {K : Type*} [CommRing K] (alpha beta p q c : K) :
    MvPolynomial.pderiv false (parabolaSection K alpha beta p q c) =
      MvPolynomial.C (2 * alpha) * MvPolynomial.X false +
        MvPolynomial.X true + MvPolynomial.C p := by
  classical
  simp [parabolaSection, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_C] <;>
    simp only [map_mul, map_natCast] <;> ring

/-- The formal y partial derivative, in all characteristics. -/
theorem pderiv_parabola_y
    {K : Type*} [CommRing K] (alpha beta p q c : K) :
    MvPolynomial.pderiv true (parabolaSection K alpha beta p q c) =
      MvPolynomial.X false +
        MvPolynomial.C (2 * beta) * MvPolynomial.X true +
        MvPolynomial.C q := by
  classical
  simp [parabolaSection, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_C] <;>
    simp only [map_mul, map_natCast] <;> ring

/-- The characteristic-free, degree-three parameter eliminant. -/
def eliminant
    {K : Type*} [CommRing K]
    (alpha beta p q c : K) : K :=
  (4 * alpha * beta - 1) * c -
    alpha * q ^ 2 - beta * p ^ 2 + p * q

/-- Global polynomial identity with actual Mathlib partial
derivatives. Its right-hand side contains no x or y variables. -/
theorem parabola_bezout_identity
    {K : Type*} [CommRing K] (alpha beta p q c : K) :
    MvPolynomial.C (eliminant alpha beta p q c) =
      MvPolynomial.C (4 * alpha * beta - 1) *
          parabolaSection K alpha beta p q c -
        MvPolynomial.C alpha *
          (MvPolynomial.pderiv true
            (parabolaSection K alpha beta p q c)) ^ 2 -
        MvPolynomial.C beta *
          (MvPolynomial.pderiv false
            (parabolaSection K alpha beta p q c)) ^ 2 +
        MvPolynomial.pderiv false
          (parabolaSection K alpha beta p q c) *
        MvPolynomial.pderiv true
          (parabolaSection K alpha beta p q c) := by
  rw [pderiv_parabola_x, pderiv_parabola_y]
  simp only [parabolaSection, eliminant, map_sub, map_add,
    map_mul, map_pow, map_one, map_natCast]
  ring

/-- A parameter is critical when the section and both actual
partial derivatives vanish at a geometric point. -/
theorem critical_implies_eliminant_zero
    {K : Type*} [CommRing K]
    (alpha beta p q c : K) (u : Bool → K)
    (hG : MvPolynomial.eval u (parabolaSection K alpha beta p q c) = 0)
    (hX : MvPolynomial.eval u
      (MvPolynomial.pderiv false
        (parabolaSection K alpha beta p q c)) = 0)
    (hY : MvPolynomial.eval u
      (MvPolynomial.pderiv true
        (parabolaSection K alpha beta p q c)) = 0) :
    eliminant alpha beta p q c = 0 := by
  have h := congrArg (MvPolynomial.eval u)
    (parabola_bezout_identity alpha beta p q c)
  simpa [hG, hX, hY] using h

/-- Polynomial coordinates of (α,β,p,q,c), in that order. -/
def parameterPoint {K : Type*}
    (alpha beta p q c : K) : Fin 5 → K :=
  fun i => if i = 0 then alpha else if i = 1 then beta
    else if i = 2 then p else if i = 3 then q else c

/-- An actual parameter MvPolynomial, independent of x,y. -/
noncomputable def badParameterPolynomial
    (K : Type*) [CommRing K] : MvPolynomial (Fin 5) K :=
  (MvPolynomial.C (4 : K) *
      MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (1 : Fin 5) - 1) *
      MvPolynomial.X (4 : Fin 5) -
    MvPolynomial.X (0 : Fin 5) * (MvPolynomial.X (3 : Fin 5)) ^ 2 -
    MvPolynomial.X (1 : Fin 5) * (MvPolynomial.X (2 : Fin 5)) ^ 2 +
    MvPolynomial.X (2 : Fin 5) * MvPolynomial.X (3 : Fin 5)

theorem eval_badParameterPolynomial
    {K : Type*} [CommRing K]
    (alpha beta p q c : K) :
    MvPolynomial.eval (parameterPoint alpha beta p q c)
      (badParameterPolynomial K) =
      eliminant alpha beta p q c := by
  simp [badParameterPolynomial, parameterPoint, eliminant]
  ring

/-- The bad-parameter polynomial is formally nonzero even over
F₂: at α=β=p=q=0, c=1 its value is -1. -/
theorem badParameterPolynomial_ne_zero
    {K : Type*} [Field K] :
    badParameterPolynomial K ≠ 0 := by
  intro hzero
  have hval :
      MvPolynomial.eval
          (parameterPoint (0 : K) 0 0 0 1)
          (badParameterPolynomial K) = -(1 : K) := by
    rw [eval_badParameterPolynomial]
    simp [eliminant]
  have hz :
      MvPolynomial.eval
          (parameterPoint (0 : K) 0 0 0 1)
          (badParameterPolynomial K) = 0 := by
    rw [hzero]
    simp
  have hcontra : -(1 : K) = 0 := hval.symm.trans hz
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)) hcontra

/-- Critical section parameters vanish on the actual formal
parameter polynomial, not merely on a finite-field function. -/
theorem critical_parameters_in_bad_hypersurface
    {K : Type*} [Field K]
    (alpha beta p q c : K) (u : Bool → K)
    (hG : MvPolynomial.eval u (parabolaSection K alpha beta p q c) = 0)
    (hX : MvPolynomial.eval u
      (MvPolynomial.pderiv false
        (parabolaSection K alpha beta p q c)) = 0)
    (hY : MvPolynomial.eval u
      (MvPolynomial.pderiv true
        (parabolaSection K alpha beta p q c)) = 0) :
    MvPolynomial.eval (parameterPoint alpha beta p q c)
      (badParameterPolynomial K) = 0 := by
  rw [eval_badParameterPolynomial]
  exact critical_implies_eliminant_zero alpha beta p q c u hG hX hY

#print axioms pderiv_parabola_x
#print axioms pderiv_parabola_y
#print axioms parabola_bezout_identity
#print axioms critical_implies_eliminant_zero
#print axioms eval_badParameterPolynomial
#print axioms badParameterPolynomial_ne_zero
#print axioms critical_parameters_in_bad_hypersurface

end Deligne17
