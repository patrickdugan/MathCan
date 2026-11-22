import Deligne04.SharpJacobianIdeal
import Deligne04.EffectiveFiniteOpen
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

/-!
# DEL-15: a relative Jacobian certificate on an actually embedded line

Fix the embedded affine line U_d = {(x,y) | y = x + d} in A².
Restrict DEL-12's actual conic F(X,Y) = XY + aX + bY + c to U_d.
The section is G(X) = X² + (d+a+b)X + bd+c.

Its actual univariate derivative is G'(X) = 2X + d+a+b. The
relative discriminant D = (d+a+b)² - 4(bd+c) obeys the global
polynomial identity (G')² - 4G = C(D). Thus D ≠ 0 provides a
Bézout certificate that (G,G') is the unit ideal, valid in
characteristic two as well as in odd characteristic.

The ambient hypersurface XY+1 is regular, but its restriction to
the embedded line y=x-2 is (X-1)² and has a critical zero at 1.
This demonstrates the need for the Jacobian of the *restriction*
rather than the ambient Jacobian in the original Bertini problem.

This is an explicit embedded-line model, not yet the arbitrary
embedded U^k of the Hexagon Lemma 8. Its Katz good open remains an
explicit separate polynomial assumption.
-/

namespace Deligne15

/-- The restriction of the conic polynomial to the embedded
affine line y=x+d, represented in the actual Polynomial ring. -/
noncomputable def graphSection (K : Type*) [CommRing K]
    (a b c d : K) : Polynomial K :=
  Polynomial.X ^ 2 +
    Polynomial.C (d + a + b) * Polynomial.X +
    Polynomial.C (b * d + c)

/-- Exact value of the restricted polynomial. -/
theorem eval_graphSection
    {K : Type*} [CommRing K] (a b c d x : K) :
    Polynomial.eval x (graphSection K a b c d) =
      x ^ 2 + (d + a + b) * x + (b * d + c) := by
  simp [graphSection]

/-- The restricted section equals the genuine two-variable
polynomial F evaluated on the graph y=x+d. -/
theorem eval_graphSection_eq_conic_restriction
    {K : Type*} [CommRing K] (a b c d x : K) :
    Polynomial.eval x (graphSection K a b c d) =
      MvPolynomial.eval (Deligne12.conicPoint x (x + d))
        (Deligne12.conicPolynomial K a b c) := by
  rw [eval_graphSection, Deligne12.eval_conicPolynomial]
  ring

/-- The actual formal derivative of the restricted polynomial. -/
theorem derivative_graphSection
    {K : Type*} [CommRing K] (a b c d : K) :
    Polynomial.derivative (graphSection K a b c d) =
      Polynomial.C (2 : K) * Polynomial.X +
        Polynomial.C (d + a + b) := by
  simp [graphSection, Polynomial.C_ofNat] <;> ring

/-- Evaluation of the actual derivative, in every characteristic. -/
theorem eval_derivative_graphSection
    {K : Type*} [CommRing K] (a b c d x : K) :
    Polynomial.eval x
        (Polynomial.derivative (graphSection K a b c d)) =
      2 * x + d + a + b := by
  rw [derivative_graphSection]
  simp
  ring

/-- The relative bad-parameter polynomial for U_d. -/
def graphDelta
    {K : Type*} [CommRing K] (a b c d : K) : K :=
  (d + a + b) ^ 2 - 4 * (b * d + c)

/-- A characteristic-independent discriminant identity at points. -/
theorem eval_discriminant_identity
    {K : Type*} [CommRing K] (a b c d x : K) :
    (2 * x + d + a + b) ^ 2 -
      4 * (x ^ 2 + (d + a + b) * x + (b * d + c)) =
        graphDelta a b c d := by
  dsimp [graphDelta]
  ring

/-- The stronger global identity holds in the true polynomial ring,
using its genuine derivative. -/
theorem relative_bezout_identity
    {K : Type*} [CommRing K] (a b c d : K) :
    (Polynomial.derivative (graphSection K a b c d)) ^ 2 -
      Polynomial.C (4 : K) * graphSection K a b c d =
        Polynomial.C (graphDelta a b c d) := by
  rw [derivative_graphSection]
  simp only [graphSection, graphDelta, map_sub, map_add,
    map_mul, map_pow, Polynomial.C_ofNat]
  ring

/-- The relative hypersurface Jacobian ideal (G,G') in K[X]. -/
noncomputable def relativeJacobianIdeal
    (K : Type*) [Field K] (a b c d : K) :
    Ideal (Polynomial K) :=
  Ideal.span ({
    graphSection K a b c d,
    Polynomial.derivative (graphSection K a b c d)
  } : Set (Polynomial K))

theorem section_mem_relative_jacobian
    {K : Type*} [Field K] (a b c d : K) :
    graphSection K a b c d ∈ relativeJacobianIdeal K a b c d := by
  apply Ideal.subset_span
  simp

theorem derivative_mem_relative_jacobian
    {K : Type*} [Field K] (a b c d : K) :
    Polynomial.derivative (graphSection K a b c d) ∈
      relativeJacobianIdeal K a b c d := by
  apply Ideal.subset_span
  simp

/-- The relative discriminant is a constant in the actual
Jacobian ideal; this is a global algebraic certificate. -/
theorem discriminant_mem_relative_jacobian
    {K : Type*} [Field K] (a b c d : K) :
    Polynomial.C (graphDelta a b c d) ∈
      relativeJacobianIdeal K a b c d := by
  let J := relativeJacobianIdeal K a b c d
  have hG : graphSection K a b c d ∈ J :=
    section_mem_relative_jacobian a b c d
  have hD : Polynomial.derivative (graphSection K a b c d) ∈ J :=
    derivative_mem_relative_jacobian a b c d
  have hDD :
      (Polynomial.derivative (graphSection K a b c d)) ^ 2 ∈ J := by
    simpa only [pow_two] using
      (J.mul_mem_left (Polynomial.derivative (graphSection K a b c d)) hD)
  have h4G :
      Polynomial.C (4 : K) * graphSection K a b c d ∈ J :=
    J.mul_mem_left _ hG
  rw [← relative_bezout_identity]
  exact J.sub_mem hDD h4G

/-- Away from the relative discriminant the global Jacobian
ideal contains 1; this implies pointwise Jacobian regularity. -/
theorem relative_jacobian_top_of_delta_nonzero
    {K : Type*} [Field K] (a b c d : K)
    (hdelta : graphDelta a b c d ≠ 0) :
    relativeJacobianIdeal K a b c d = ⊤ := by
  let J := relativeJacobianIdeal K a b c d
  have hc : Polynomial.C (graphDelta a b c d) ∈ J :=
    discriminant_mem_relative_jacobian a b c d
  have hmul :
      Polynomial.C ((graphDelta a b c d)⁻¹) *
        Polynomial.C (graphDelta a b c d) ∈ J :=
    J.mul_mem_left _ hc
  have hvalue :
      Polynomial.C ((graphDelta a b c d)⁻¹) *
        Polynomial.C (graphDelta a b c d) =
          (1 : Polynomial K) := by
    rw [← map_mul, inv_mul_cancel₀ hdelta, map_one]
  rw [hvalue] at hmul
  exact (Ideal.eq_top_iff_one J).mpr hmul

/-- Every critical point of the restriction lies over D=0.
The implication is valid without assuming algebraic closure. -/
theorem critical_implies_discriminant_zero
    {K : Type*} [CommRing K] (a b c d x : K)
    (hG : Polynomial.eval x (graphSection K a b c d) = 0)
    (hD : Polynomial.eval x
      (Polynomial.derivative (graphSection K a b c d)) = 0) :
    graphDelta a b c d = 0 := by
  rw [eval_graphSection] at hG
  rw [eval_derivative_graphSection] at hD
  have hid := eval_discriminant_identity a b c d x
  rw [hG, hD] at hid
  simpa using hid.symm

theorem regular_off_discriminant
    {K : Type*} [CommRing K] (a b c d : K)
    (hdelta : graphDelta a b c d ≠ 0) :
    ∀ x : K,
      Polynomial.eval x (graphSection K a b c d) = 0 →
      Polynomial.eval x
        (Polynomial.derivative (graphSection K a b c d)) ≠ 0 := by
  intro x hG hD
  exact hdelta (critical_implies_discriminant_zero a b c d x hG hD)

/-- Coordinates (a,b,c,d) occupy indices 0,1,2,3. -/
def parameterPoint {K : Type*} [Zero K] [One K]
    (a b c d : K) : Fin 4 → K :=
  fun i => if i = 0 then a else if i = 1 then b
    else if i = 2 then c else d

/-- A genuine multivariate polynomial cutting out the relative
bad-discriminant locus for the embedded-line family. -/
noncomputable def badParameterPolynomial
    (K : Type*) [CommRing K] : MvPolynomial (Fin 4) K :=
  (MvPolynomial.X (3 : Fin 4) + MvPolynomial.X (0 : Fin 4) +
    MvPolynomial.X (1 : Fin 4)) ^ 2 -
    MvPolynomial.C (4 : K) *
      (MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) +
        MvPolynomial.X (2 : Fin 4))

theorem eval_badParameterPolynomial
    {K : Type*} [CommRing K] (u : Fin 4 → K) :
    MvPolynomial.eval u (badParameterPolynomial K) =
      (u 3 + u 0 + u 1) ^ 2 - 4 * (u 1 * u 3 + u 2) := by
  simp [badParameterPolynomial]

theorem eval_badParameter_at_parameters
    {K : Type*} [CommRing K] (a b c d : K) :
    MvPolynomial.eval (parameterPoint a b c d)
      (badParameterPolynomial K) = graphDelta a b c d := by
  rw [eval_badParameterPolynomial]
  simp [parameterPoint, graphDelta]

/-- D is nonzero even over F2; at (a,b,c,d)=(1,0,0,0)
its value is exactly 1. -/
theorem badParameterPolynomial_ne_zero
    {K : Type*} [Field K] :
    badParameterPolynomial K ≠ 0 := by
  intro hz
  have hv :
      MvPolynomial.eval (parameterPoint (1 : K) 0 0 0)
        (badParameterPolynomial K) = (1 : K) := by
    rw [eval_badParameter_at_parameters]
    norm_num [graphDelta]
  have hzv :
      MvPolynomial.eval (parameterPoint (1 : K) 0 0 0)
        (badParameterPolynomial K) = 0 := by
    rw [hz]
    simp
  rw [hv] at hzv
  exact one_ne_zero hzv

/-- The exact relative polynomial can be combined with a supplied
Katz principal-open polynomial using DEL-10's finite-field theorem.
The Katz polynomial and degree budget remain explicit inputs. -/
theorem exists_relative_regular_and_katz_good
    {K : Type*} [Field K] [Fintype K]
    (L : MvPolynomial (Fin 4) K)
    (hL : L ≠ 0)
    (hbudget : ∀ i : Fin 4,
      (badParameterPolynomial K).degreeOf i + L.degreeOf i <
        Fintype.card K) :
    ∃ u : Fin 4 → K,
      (∀ x : K,
        Polynomial.eval x (graphSection K (u 0) (u 1) (u 2) (u 3)) = 0 →
        Polynomial.eval x
          (Polynomial.derivative
            (graphSection K (u 0) (u 1) (u 2) (u 3))) ≠ 0) ∧
      MvPolynomial.eval u L ≠ 0 := by
  obtain ⟨u, hdelta, hLval⟩ :=
    Deligne10.exists_point_in_two_good_opens
      (badParameterPolynomial K) L
      badParameterPolynomial_ne_zero hL hbudget
  refine ⟨u, ?_, hLval⟩
  apply regular_off_discriminant
  rw [eval_badParameterPolynomial] at hdelta
  exact hdelta

/-- Explicit counterexample: F=XY+1 is regular in ambient A²,
but on the embedded line y=x-2 the section is (X-1)². -/
theorem tangent_example_ambient_jacobian_top
    {K : Type*} [Field K] :
    Deligne13.conicJacobianIdeal K 0 0 1 = ⊤ := by
  rw [Deligne14.conic_jacobian_ideal_top_iff]
  simp

theorem tangent_example_section_zero
    {K : Type*} [CommRing K] :
    Polynomial.eval (1 : K) (graphSection K 0 0 1 (-2)) = 0 := by
  rw [eval_graphSection]
  ring

theorem tangent_example_derivative_zero
    {K : Type*} [CommRing K] :
    Polynomial.eval (1 : K)
      (Polynomial.derivative (graphSection K 0 0 1 (-2))) = 0 := by
  rw [eval_derivative_graphSection]
  ring

theorem tangent_example_bad_delta
    {K : Type*} [CommRing K] :
    graphDelta (0 : K) 0 1 (-2) = 0 := by
  dsimp [graphDelta]
  ring

theorem tangent_example_ambient_point_regular
    {K : Type*} [Field K] :
    MvPolynomial.eval (Deligne12.conicPoint (1 : K) (-1))
      (MvPolynomial.pderiv true (Deligne12.conicPolynomial K 0 0 1))
        ≠ 0 := by
  rw [Deligne12.eval_pderiv_conic_y]
  simp

#print axioms eval_graphSection
#print axioms eval_graphSection_eq_conic_restriction
#print axioms derivative_graphSection
#print axioms eval_derivative_graphSection
#print axioms relative_bezout_identity
#print axioms discriminant_mem_relative_jacobian
#print axioms relative_jacobian_top_of_delta_nonzero
#print axioms critical_implies_discriminant_zero
#print axioms eval_badParameterPolynomial
#print axioms badParameterPolynomial_ne_zero
#print axioms exists_relative_regular_and_katz_good
#print axioms tangent_example_ambient_jacobian_top
#print axioms tangent_example_section_zero
#print axioms tangent_example_derivative_zero
#print axioms tangent_example_ambient_point_regular

end Deligne15
