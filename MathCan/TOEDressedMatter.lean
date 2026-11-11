import Init

/-!
# TOE-05: trace-free FLRW matter identities and conditional closure

The source is Bianconi, Lambda-Gravity from Entropy (2026),
Eqs. (5), (7), (16), (45)--(49).

This Lean module proves the exact *algebraic* consequences of the dressed
trace-free field equation, its vacuum-shift invariance, and the positivity
logic used in the Schur-complement closure certificate. The logarithmic
Lagrangian, scalar Euler-Lagrange equation, and numerical ODE solver are
written derivations tested by independent finite calculations. They are not
Lean-proved field equations or a proof of full covariant tensor refinement.
-/

namespace MathCan.TOEDressedMatter

/-- One scalar, one temporal vector, three spatial vectors,
three temporal bivectors and three spatial bivectors. -/
theorem spectral_multiplicity : 1 + 1 + 3 + 3 + 3 = 11 := by omega

/-- The geometric trace for X_00=x0, X_ij=a² xs δ_ij. -/
def trace (x0 xs : Int) : Int := -x0 + 3 * xs

/-- Multiplying the temporal trace-free projection by four. -/
theorem temporal_projector (x0 xs : Int) :
    4 * x0 + trace x0 xs = 3 * (x0 + xs) := by
  simp only [trace]
  omega

/-- The spatial trace-free projection has the same enthalpy combination. -/
theorem spatial_projector (x0 xs : Int) :
    4 * xs - trace x0 xs = x0 + xs := by
  simp only [trace]
  omega

/-- In Bianconi Eq.(47), let K denote κ times the dressed enthalpy (ρ+p).
The 00 equation is equivalent to X0+Xs = 3 K. -/
theorem flrw_temporal_tracefree_iff (x0 xs K : Int) :
    4*x0 + trace x0 xs = 9*K ↔ x0 + xs = 3*K := by
  simp only [trace]
  omega

/-- The trace-free spatial component is fixed once the temporal component
and the two component traces are consistent. -/
theorem flrw_spatial_tracefree_from_temporal (x0 xs K : Int)
    (h : 4*x0 + trace x0 xs = 9*K) :
    4*xs - trace x0 xs = 3*K := by
  simp only [trace] at *
  omega

/-- A vacuum-like addition shifts rho by v and pressure by minus v,
so the dressed enthalpy is unchanged in the trace-free field equation. -/
theorem metric_vacuum_shift (rho pressure vacuum : Int) :
    (rho + vacuum) + (pressure - vacuum) = rho + pressure := by
  omega

/-- A constant term proportional to the metric has a zero traceless part.
Its time component is v and its spatial component is -v. -/
theorem metric_tensor_tracefree_zero (vacuum : Int) :
    4*vacuum + trace vacuum (-vacuum) = 0 := by
  simp only [trace]
  omega

/-- The source coefficient alpha/(3 beta)=2 kappa implies alpha=6*kappa*beta
at the algebraic level, after alpha is supplied as 6 times the product. -/
theorem gr_coupling_normalization (kappaBeta : Int) :
    6*kappaBeta = 3*(2*kappaBeta) := by
  omega

/-- The first-order lapse relation in units where kappa is absorbed into
kinetic and mass contributions yields the usual Friedmann normalization. -/
theorem gr_lapse_limit (H2 Lambda kinetic massEnergy : Int)
    (h : 18*H2-6*Lambda-6*kinetic-6*massEnergy=0) :
    3*H2 = Lambda + kinetic + massEnergy := by
  omega

/-- A positive central Schur contribution and a nonnegative peripheral
term certify strict positivity of their sum. -/
theorem schur_positive_of_components (center peripheral : Int)
    (hc : 0 < center) (hp : 0 ≤ peripheral) :
    0 < center + peripheral := by omega

/-- A nonzero determinant gives uniqueness once elimination reduces the
homogeneous difference system to determinant times each difference = 0. -/
theorem determinant_unique_difference (det difference : Int)
    (hd : det ≠ 0) (heq : det * difference = 0) : difference = 0 := by
  rcases mul_eq_zero.mp heq with hz | hz
  · exact False.elim (hd hz)
  · exact hz

/-- Weyl trace equation and joint Noether compatibility imply on-shell
constancy of the cosmological multiplier. The variables are time derivatives
of R_G, D, κT, Λ_G, and Λ respectively, with no separate matter conservation
assumption. -/
theorem lambda_stationary_from_joint_identity
    (dRG dD dKT dLambdaG dLambda : Int)
    (traceRelation : 12*dLambda = dRG - dD + 3*dKT - 12*dLambdaG)
    (jointNoether : dRG - dD + 3*dKT - 12*dLambdaG = 0) :
    dLambda = 0 := by omega

/-- The linearized scalar equation has the conventional Klein-Gordon
bracket d(pi)/dt+3H pi+m² phi; this is an algebraic normalization only. -/
theorem scalar_kg_normalization (piDot friction massForce : Int) :
    2*(piDot+friction+massForce)=2*piDot+2*friction+2*massForce := by
  omega

#print axioms spectral_multiplicity
#print axioms temporal_projector
#print axioms spatial_projector
#print axioms flrw_temporal_tracefree_iff
#print axioms flrw_spatial_tracefree_from_temporal
#print axioms metric_vacuum_shift
#print axioms metric_tensor_tracefree_zero
#print axioms gr_coupling_normalization
#print axioms gr_lapse_limit
#print axioms schur_positive_of_components
#print axioms determinant_unique_difference
#print axioms lambda_stationary_from_joint_identity
#print axioms scalar_kg_normalization

end MathCan.TOEDressedMatter
