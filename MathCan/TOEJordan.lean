import MathCan.TOEMixedPrincipal

/-!
# TOE-12: Jordan obstruction and algebraic gauge/auxiliary-field identities

The exact 6×6 rational companion calculation is executed by
research/toe/jordan_principal.py; the kernel statements below prove general
structural implications of a repeated characteristic, the two-component
Jordan block, the Abelianized principal gauge quotient, and the scalar
inverse-map first variation. They do NOT formalize all six-by-six rational
matrix entries or establish full Lambda-GfE strong hyperbolicity.
-/

namespace MathCan.TOEJordan

/-- Quartic metric factor, written as a quadratic in x=omega². -/
def metricFactor (a x r : Int) : Int := a * ((x-r)*(x-r))

/-- Odd metric/gauge mixed factor after removing the frequency. -/
def mixedFactor (b x r : Int) : Int := b * (x-r)

theorem metric_vanishes_at_double_root (a r : Int) :
    metricFactor a r r = 0 := by simp [metricFactor]

theorem mixed_vanishes_at_double_root (b r : Int) :
    mixedFactor b r r = 0 := by simp [mixedFactor]

/-- The derivative of a(x-r)² is 2a(x-r), also zero at r. -/
theorem metric_derivative_vanishes_at_root (a r : Int) :
    2*a*(r-r) = 0 := by simp

/-- When the gauge diagonal block is nonzero, a null vector of the
    projected matrix at the repeated root has zero gauge component. -/
theorem rank_one_root_kernel (gauge diagonalComponent : Int)
    (hg : gauge ≠ 0) (h : gauge * diagonalComponent = 0) :
    diagonalComponent = 0 := by
  rcases Int.mul_eq_zero.mp h with hz | hd
  · exact False.elim (hg hz)
  · exact hd

/-- A model nilpotent Jordan-step acting on a two-component integer vector. -/
def jordanStep (v : Int × Int) : Int × Int := (v.2, 0)

theorem jordan_step_square_zero (v : Int × Int) :
    jordanStep (jordanStep v) = (0, 0) := by
  rfl

theorem jordan_step_nonzero : jordanStep (0, 1) ≠ (0, 0) := by
  decide

/-- In the 2×2 Jordan normal form J=[lambda,1;0,lambda], the (0,1)
    component of SJ=J^T S implies S_00=0. -/
theorem jordan_selfadjoint_forces_zero (s00 s01 lambda : Int)
    (h : s00 + s01*lambda = lambda*s01) : s00 = 0 := by
  rw [Int.mul_comm lambda s01] at h
  omega

/-- A positive-definite symmetrizer would have S_00>0, contradicting
    the Jordan self-adjointness equation. -/
theorem jordan_has_no_positive_symmetrizer (s00 s01 lambda : Int)
    (hp : 0 < s00) :
    ¬ (s00 + s01*lambda = lambda*s01) := by
  intro h
  have hz := jordan_selfadjoint_forces_zero s00 s01 lambda h
  omega

/-- A proposed omitted-sector correction epsilon*(x-r) gives a simple
    determinant root when epsilon and the remaining gauge factor are nonzero. -/
theorem separated_root_first_derivative_nonzero (epsilon gauge : Int)
    (he : epsilon ≠ 0) (hg : gauge ≠ 0) :
    epsilon * gauge ≠ 0 := by
  intro hz
  rcases Int.mul_eq_zero.mp hz with h | h
  · exact he h
  · exact hg h

/-- A one-form proportional to its wave covector has zero exterior square. -/
theorem proportional_wave_wedge_zero (xi xj scale : Int) :
    xi*(scale*xj) - xj*(scale*xi) = 0 := by
  have h : xi*(scale*xj) = xj*(scale*xi) := by ac_rfl
  rw [h]
  omega

/-- A nonzero wave-component pivot gives a cross-multiplied description
    of the kernel of the gauge wedge map; division belongs to the Q oracle. -/
theorem gauge_pivot_kernel (xiPivot xiOther aPivot aOther : Int)
    (hw : xiPivot*aOther - xiOther*aPivot = 0) :
    xiPivot*aOther = xiOther*aPivot := by
  omega

/-- A longitudinal shift preserves the field-strength symbol. -/
theorem gauge_shift_invariant_wedge (xi xj ai aj scale : Int) :
    xi*(aj+scale*xj) - xj*(ai+scale*xi) = xi*aj-xj*ai := by
  have hc : xi*(scale*xj) = xj*(scale*xi) := by ac_rfl
  calc
    xi*(aj+scale*xj) - xj*(ai+scale*xi)
      = (xi*aj+xi*(scale*xj))-(xj*ai+xj*(scale*xi)) := by
          rw [Int.mul_add, Int.mul_add]
    _ = xi*aj - xj*ai := by rw [hc]; omega

/-- The scalar version of D(G)= -G (D Theta) G when Theta*G=1.
    The full 6x6 noncommutative identity is checked with exact rational
    matrices by research/toe/gfield_linearization.py. -/
theorem scalar_auxiliary_inverse_constraint (theta g dtheta : Int)
    (hinv : theta*g = 1) :
    theta * (-(g*dtheta*g)) + dtheta*g = 0 := by
  have h : theta*(g*dtheta*g)=dtheta*g := by
    calc
      theta*(g*dtheta*g) = (theta*g)*(dtheta*g) := by ac_rfl
      _ = 1*(dtheta*g) := by rw [hinv]
      _ = dtheta*g := by simp
  rw [Int.mul_neg, h]
  omega

/-- Six independent adjoint colors each carry four gauge amplitudes;
    the bare gauge wedge removes one and the null Gauss constraint one. -/
theorem bare_su2_doublet_transverse_count : 6*(4-1-1)=12 := by omega

#print axioms metric_vanishes_at_double_root
#print axioms mixed_vanishes_at_double_root
#print axioms metric_derivative_vanishes_at_root
#print axioms rank_one_root_kernel
#print axioms jordan_step_square_zero
#print axioms jordan_step_nonzero
#print axioms jordan_selfadjoint_forces_zero
#print axioms jordan_has_no_positive_symmetrizer
#print axioms separated_root_first_derivative_nonzero
#print axioms proportional_wave_wedge_zero
#print axioms gauge_pivot_kernel
#print axioms gauge_shift_invariant_wedge
#print axioms scalar_auxiliary_inverse_constraint
#print axioms bare_su2_doublet_transverse_count

end MathCan.TOEJordan
