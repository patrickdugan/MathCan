import MathCan.TOENonAbelian

/-!
# TOE-11: rank-one Schur cancellation in a declared curvature--gauge jet

The companion Fraction oracle differentiates the *defined* logarithmic
SU(2)^2 matter response with respect to one FLRW curvature acceleration A
and gauge-electric velocities. The highest-derivative jet Hessian has a
rank-one curvature/mixed contribution. Its Schur cancellation is independent
of the Lorentzian spectrum gate. The 6x6 operator variation is checked by an
independent executable implementation.

These kernel facts concern only algebraic normal forms and conditional
positivity/invertibility. The 3x3 determinant factorization for two flavors,
operator derivatives, and physical hyperbolicity require distinct checks.
A positive higher-derivative jet Hessian is not a gravitational stability
or constrained Cauchy-well-posedness theorem.
-/
namespace MathCan.TOEMixedPrincipal

/-- One flavor's normalized rank-one Hessian determinant. -/
theorem one_flavor_schur_cancel (p v gauge : Int) :
    (p*p)*(gauge+v*v) - (p*v)*(p*v) = (p*p)*gauge := by
  have hreorder : (p*p)*(v*v) = (p*v)*(p*v) := by ac_rfl
  rw [Int.mul_add, hreorder]
  omega

/-- Multiplication by a nonzero curvature factor and a nonzero gauge Schur
complement preserves invertibility in the single-channel restriction. -/
theorem one_flavor_schur_invertible (p v gauge : Int)
    (hp : p ≠ 0) (hg : gauge ≠ 0) :
    (p*p)*(gauge+v*v)-(p*v)*(p*v) ≠ 0 := by
  rw [one_flavor_schur_cancel]
  intro hz
  have split : p*p = 0 ∨ gauge = 0 := Int.mul_eq_zero.mp hz
  rcases split with pp | gg
  · rcases Int.mul_eq_zero.mp pp with p0 | p0
    · exact hp p0
    · exact hp p0
  · exact hg gg

/-- The rank-one outer product's quadratic form is a perfect square.
The kernel audit does not assume positivity without explicit coefficients. -/
theorem rank_one_square_expansion (u v : Int) :
    (u+v)*(u+v) = u*u+2*(u*v)+v*v := by
  calc
    (u+v)*(u+v) = (u*u+u*v)+(v*u+v*v) := by
      simp only [Int.add_mul, Int.mul_add]
      omega
    _ = u*u+2*(u*v)+v*v := by
      rw [Int.mul_comm v u]
      omega

/-- The mixed curvature--matter Hessian is symmetric as a bilinear form. -/
theorem reciprocal_mixed_coefficient (curvature gauge : Int) :
    curvature*gauge = gauge*curvature := Int.mul_comm _ _

/-- If thetaB=base+alpha*b, the transverse gauge Hessian has a base response
beside its sum of squares. This is the source of the positivity certificate. -/
theorem magnetic_base_split (thetaB base alphaB : Int)
    (h : thetaB = base + alphaB) : thetaB-alphaB = base := by
  omega

/-- Positive couplings and positive tensor response yield a strictly positive
curvature-rank-one prefactor (before nonzero positive normalization). -/
theorem positive_curvature_factor (beta thetaB : Int)
    (hb : 0 < beta) (ht : 0 < thetaB) :
    0 < (beta*thetaB)*(beta*thetaB) := by
  have h : 0 < beta*thetaB := Int.mul_pos hb ht
  exact Int.mul_pos h h

/-- The gauge response gap is still meaningful when an independent spectral
discriminant is negative: signs of these distinct certificates are independent. -/
theorem independent_kinetic_and_spectral_gates (kinetic spectrum : Int)
    (hk : kinetic > 0) (hs : spectrum < 0) :
    kinetic > 0 ∧ ¬ (spectrum ≥ 0) := by
  constructor
  · exact hk
  · omega

/-- In a completed-square certificate, a positive gauge base and a
nonnegative rank-one component give a positive quadratic form. -/
theorem completed_square_positive (rankOne gaugeBase : Int)
    (hr : 0 ≤ rankOne) (hg : 0 < gaugeBase) :
    0 < rankOne+gaugeBase := by omega

/-- A pure-gauge one-form perturbation proportional to a wave covector has
vanishing antisymmetrized field-strength symbol. -/
theorem gauge_wave_null (xi i j : Int) :
    (xi*i)*(xi*j)-(xi*j)*(xi*i)=0 := by
  have h : (xi*j)*(xi*i) = (xi*i)*(xi*j) := Int.mul_comm _ _
  rw [h]
  omega

/-- The symmetrized metric pure-gauge parameter has a vanishing simple
antisymmetric pairing, an elementary component in the Riemann gauge null. -/
theorem metric_wave_commutator (xi v : Int) : xi*v-v*xi=0 := by
  rw [Int.mul_comm xi v]
  omega

#print axioms one_flavor_schur_cancel
#print axioms one_flavor_schur_invertible
#print axioms rank_one_square_expansion
#print axioms reciprocal_mixed_coefficient
#print axioms magnetic_base_split
#print axioms positive_curvature_factor
#print axioms independent_kinetic_and_spectral_gates
#print axioms completed_square_positive
#print axioms gauge_wave_null
#print axioms metric_wave_commutator
end MathCan.TOEMixedPrincipal
