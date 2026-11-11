import MathCan.TOEDressedMatter

/-!
# TOE-06: FLRW covariant projections and conditional tensor-cone gates

These kernel theorems concern algebraic Ricci projections, Weyl normalization,
and strict-principal sum-of-squares logic. The physical TT symbol was derived
by Pereira (arXiv:2609.03082) under explicit single-multiplet hypotheses.
The scalar trajectory, its spacetime derivative tensors and exact 4D dressed
stress tensor are not thereby kernel-certified.
-/
namespace MathCan.TOECovariantGates

/-- Flat or curved FLRW: R_00=-3A and R_spatial=A+2B. -/
theorem ricci_scalar_trace (A B : Int) :
    -(-3*A) + 3*(A+2*B) = 6*(A+B) := by omega

/-- Twice the temporal trace-free Ricci component is 3(B-A). -/
theorem doubled_tracefree_temporal (A B : Int) :
    2*(-3*A) + 3*(A+B) = 3*(B-A) := by omega

/-- Twice the spatial trace-free Ricci coefficient is B-A. -/
theorem doubled_tracefree_spatial (A B : Int) :
    2*(A+2*B) - 3*(A+B) = B-A := by omega

/-- The two trace-free components cancel under metric contraction. -/
theorem traceless_tensor_contraction (d : Int) :
    -(3*d) + 3*d = 0 := by omega

/-- The eleven-dimensional form-sector curvature trace equals 3 times the
spacetime scalar curvature at unit response. -/
theorem form_space_curvature_trace (A B : Int) :
    6*(A+B) + 3*A + 3*(A+2*B) + 3*(2*A) + 3*(2*B)
      = 18*(A+B) := by omega

/-- The difference of the denominators of magnetic and electric bivector
responses is proportional to the spacetime Einstein-locus defect. -/
theorem bivector_inverse_denominator_gap (beta A B : Int) :
    (1-2*beta*B) - (1-2*beta*A) = 2*beta*(A-B) := by
  simp only [Int.mul_sub]
  omega

/-- Positive weighted strict-principal squares can sum to zero only if each
nonnegative square contribution is zero. The physical assignment of the
square terms is a separate theorem hypothesis. -/
theorem positive_two_square_zero (a b x2 y2 : Int)
    (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x2) (hy : 0 ≤ y2)
    (h : a*x2 + b*y2 = 0) : x2 = 0 ∧ y2 = 0 := by
  have hax : 0 ≤ a*x2 := Int.mul_nonneg (le_of_lt ha) hx
  have hby : 0 ≤ b*y2 := Int.mul_nonneg (le_of_lt hb) hy
  have hzx : a*x2 = 0 := by omega
  have hzy : b*y2 = 0 := by omega
  constructor
  · rcases Int.mul_eq_zero.mp hzx with hz | hz
    · omega
    · exact hz
  · rcases Int.mul_eq_zero.mp hzy with hz | hz
    · omega
    · exact hz

/-- If the first principal square enforces omega²=p², and the second enforces
WE*omega²=WB*p² at nonzero spatial momentum, the two responses coincide. -/
theorem matched_cone_forces_equal_response
    (WE WB omega2 p2 : Int)
    (lightCone : omega2 = p2)
    (secondCone : WE*omega2 = WB*p2)
    (nonzeroMomentum : p2 ≠ 0) : WE = WB := by
  rw [lightCone] at secondCone
  have hz : (WE-WB)*p2 = 0 := by
    rw [Int.sub_mul]
    omega
  rcases Int.mul_eq_zero.mp hz with hgap | hmomentum
  · omega
  · exact False.elim (nonzeroMomentum hmomentum)

/-- A strictly positive square-product forces a negative discriminant. -/
theorem tensor_discriminant_negative (squareProduct : Int)
    (positive : 0 < squareProduct) : -4*squareProduct < 0 := by omega

/-- Weyl-stationarity trace relation in normalized 12Λ form. -/
theorem weyl_trace_rearrange
    (Lambda LambdaG RG D kT : Int)
    (h : 12*(Lambda+LambdaG)-RG+D-3*kT = 0) :
    12*(Lambda+LambdaG) = RG-D+3*kT := by omega

/-- The trace-free source equation depends only on dressed enthalpy. -/
theorem dressed_enthalpy_vacuum_shift (rho pressure vacuum : Int) :
    (rho+vacuum)+(pressure-vacuum) = rho+pressure := by omega

/-- The leading GR scalar curvature trace on form space is 3R. -/
theorem form_trace_normalization (scalarCurvature formTrace : Int)
    (h : formTrace = 3*scalarCurvature) :
    2*formTrace = 6*scalarCurvature := by omega

#print axioms ricci_scalar_trace
#print axioms doubled_tracefree_temporal
#print axioms doubled_tracefree_spatial
#print axioms traceless_tensor_contraction
#print axioms form_space_curvature_trace
#print axioms bivector_inverse_denominator_gap
#print axioms positive_two_square_zero
#print axioms matched_cone_forces_equal_response
#print axioms tensor_discriminant_negative
#print axioms weyl_trace_rearrange
#print axioms dressed_enthalpy_vacuum_shift
#print axioms form_trace_normalization

end MathCan.TOECovariantGates
