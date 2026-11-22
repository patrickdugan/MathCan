import Deligne04.BilinearBadLocus
import Deligne04.BipartiteSmoothness
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# DEL-12: genuine multivariate partial derivatives of the conic family

We now use Mathlib's actual MvPolynomial.pderiv derivations, rather
than declaring formal gradient components externally.

For F(x,y)=xy+ax+by+c we prove
  ∂F/∂x = y+a,     ∂F/∂y = x+b
in every commutative ring, including characteristic two.

Over a field, the singular incidence is precisely c=a*b. The
calculation is an actual multivariate polynomial identity; a
scheme-level Jacobian criterion is still required to conclude
smoothness of the associated quotient ring.
-/

namespace Deligne12

/-- The actual two-variable polynomial, using Bool for x and y. -/
noncomputable def conicPolynomial (K : Type*) [CommRing K]
    (a b c : K) : MvPolynomial Bool K :=
  MvPolynomial.X false * MvPolynomial.X true +
    MvPolynomial.C a * MvPolynomial.X false +
    MvPolynomial.C b * MvPolynomial.X true +
    MvPolynomial.C c

/-- Coordinates of the point (x,y) in the Bool-index polynomial ring. -/
def conicPoint {K : Type*} (x y : K) : Bool → K
  | false => x
  | true => y

/-- Evaluation reproduces the original conic phase. -/
theorem eval_conicPolynomial
    {K : Type*} [CommRing K] (a b c x y : K) :
    MvPolynomial.eval (conicPoint x y) (conicPolynomial K a b c) =
      x * y + a * x + b * y + c := by
  simp [conicPolynomial, conicPoint]

/-- Exact derivative with respect to the x-coordinate. -/
theorem pderiv_conic_x
    {K : Type*} [CommRing K] (a b c : K) :
    MvPolynomial.pderiv false (conicPolynomial K a b c) =
      MvPolynomial.X true + MvPolynomial.C a := by
  classical
  simp [conicPolynomial, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_C]

/-- Exact derivative with respect to the y-coordinate. -/
theorem pderiv_conic_y
    {K : Type*} [CommRing K] (a b c : K) :
    MvPolynomial.pderiv true (conicPolynomial K a b c) =
      MvPolynomial.X false + MvPolynomial.C b := by
  classical
  simp [conicPolynomial, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_C]

/-- Evaluation of the true x-partial derivative. -/
theorem eval_pderiv_conic_x
    {K : Type*} [CommRing K] (a b c x y : K) :
    MvPolynomial.eval (conicPoint x y)
      (MvPolynomial.pderiv false (conicPolynomial K a b c)) =
        y + a := by
  rw [pderiv_conic_x]
  simp [conicPoint]

/-- Evaluation of the true y-partial derivative. -/
theorem eval_pderiv_conic_y
    {K : Type*} [CommRing K] (a b c x y : K) :
    MvPolynomial.eval (conicPoint x y)
      (MvPolynomial.pderiv true (conicPolynomial K a b c)) =
        x + b := by
  rw [pderiv_conic_y]
  simp [conicPoint]

/-- The actual Jacobian critical-point incidence eliminates to
the same discriminant as DEL-11's finite bilinear model. -/
theorem actual_jacobian_critical_iff
    {K : Type*} [Field K] (a b c : K) :
    (∃ x y : K,
      MvPolynomial.eval (conicPoint x y)
        (conicPolynomial K a b c) = 0 ∧
      MvPolynomial.eval (conicPoint x y)
        (MvPolynomial.pderiv false (conicPolynomial K a b c)) = 0 ∧
      MvPolynomial.eval (conicPoint x y)
        (MvPolynomial.pderiv true (conicPolynomial K a b c)) = 0) ↔
      c = a * b := by
  constructor
  · rintro ⟨x, y, hphase, hx, hy⟩
    apply (Deligne08.hyperbola_singular_iff a b c).mp
    refine ⟨x, y, ?_, ?_, ?_⟩
    · simpa only [eval_conicPolynomial] using hphase
    · simpa only [eval_pderiv_conic_y] using hy
    · simpa only [eval_pderiv_conic_x] using hx
  · intro hc
    obtain ⟨x, y, hphase, hy, hx⟩ :=
      (Deligne08.hyperbola_singular_iff a b c).mpr hc
    refine ⟨x, y, ?_, ?_, ?_⟩
    · simpa only [eval_conicPolynomial] using hphase
    · simpa only [eval_pderiv_conic_x] using hx
    · simpa only [eval_pderiv_conic_y] using hy

/-- Off the discriminant, the true polynomial's two partial
derivatives cannot vanish together on its zero locus. This is
the condition needed by the affine hypersurface Jacobian criterion. -/
theorem actual_jacobian_regular_off_discriminant
    {K : Type*} [Field K] (a b c : K)
    (hdisc : c ≠ a * b) :
    ∀ x y : K,
      MvPolynomial.eval (conicPoint x y) (conicPolynomial K a b c) = 0 →
      MvPolynomial.eval (conicPoint x y)
        (MvPolynomial.pderiv false (conicPolynomial K a b c)) ≠ 0 ∨
      MvPolynomial.eval (conicPoint x y)
        (MvPolynomial.pderiv true (conicPolynomial K a b c)) ≠ 0 := by
  intro x y hzero
  by_contra h
  push Not at h
  apply hdisc
  exact (actual_jacobian_critical_iff a b c).mp
    ⟨x, y, hzero, h.1, h.2⟩

#print axioms eval_conicPolynomial
#print axioms pderiv_conic_x
#print axioms pderiv_conic_y
#print axioms eval_pderiv_conic_x
#print axioms eval_pderiv_conic_y
#print axioms actual_jacobian_critical_iff
#print axioms actual_jacobian_regular_off_discriminant

end Deligne12
