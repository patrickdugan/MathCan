import Init

/-!
# TOE-04: finite spectral multiplicities and FLRW curvature trace checks

This module verifies *algebraic* coefficients in the isotropic reduction of
GfE: the flattened 0-, 1-, and 2-form traces, and the quadratic-curvature
identity. The analytic logarithmic action, lapse variation, and ODE evolution
are written derivations with numerical tests in the accompanying research note;
those results have not yet been formalized in Lean.
-/

namespace MathCan.TOEFLRW

/-- The one scalar, one temporal vector, three spatial vectors, and six
    two-form components form the 11-dimensional flattened space. -/
theorem form_degeneracies : 1 + 1 + 3 + 3 + 3 = 11 := by omega

/-- In FRW, the mixed Ricci eigenvalues have multiplicities one and three. -/
theorem ricci_eigen_trace (A B : Int) :
    3*A + 3*(A+2*B) = 6*(A+B) := by omega

/-- The six two-form curvature eigenvalues reproduce the scalar curvature
    after accounting for the bivector normalization by a factor of two. -/
theorem bivector_eigen_trace (A B : Int) :
    3*(2*A) + 3*(2*B) = 6*(A+B) := by omega

/-- Linearized flattened trace is 3 R = 18(A+B), matching the GfE GR limit. -/
theorem flattened_first_order (A B : Int) :
    6*(A+B) + 3*A + 3*(A+2*B) + 3*(2*A) + 3*(2*B) =
    18*(A+B) := by omega

/-- Coefficients represent AA*A² + AB*A*B + BB*B². -/
structure Quadratic where
  aa : Int
  ab : Int
  bb : Int
  deriving Repr, DecidableEq

/-- Squaring the eigenvalue cA*A+cB*B with degeneracy w. -/
def weightedSquare (w cA cB : Int) : Quadratic :=
  ⟨w*cA*cA, 2*w*cA*cB, w*cB*cB⟩

def qAdd (a b : Quadratic) : Quadratic :=
  ⟨a.aa + b.aa, a.ab + b.ab, a.bb + b.bb⟩

/-- Sum over the scalar, vector and bivector curvature sectors. -/
def flattenedSquare : Quadratic :=
  qAdd (weightedSquare 1 6 6)
    (qAdd (weightedSquare 1 3 0)
      (qAdd (weightedSquare 3 1 2)
        (qAdd (weightedSquare 3 2 0) (weightedSquare 3 0 2))))

/-- Squared Ricci tensor, one time component plus three spatial components. -/
def ricciSquare : Quadratic :=
  qAdd (weightedSquare 1 3 0) (weightedSquare 3 1 2)

/-- The flattened Hessian/curvature trace has coefficients (60,84,60). -/
theorem flattened_square_coeffs : flattenedSquare = ⟨60,84,60⟩ := by rfl

theorem ricci_square_coeffs : ricciSquare = ⟨12,12,12⟩ := by rfl

/-- Evaluate any quadratic coefficient triple on independent monomials.
    Passing AA=A*A, AB=A*B, BB=B*B produces its actual polynomial value. -/
def evaluate (p : Quadratic) (AA AB BB : Int) : Int :=
  p.aa*AA + p.ab*AB + p.bb*BB

/-- On a 4D FLRW geometry the quadratic flattened curvature trace is
    5 Ricci_{mu nu} Ricci^{mu nu} + Gauss-Bonnet; GB=24 A B.

    The theorem is phrased for arbitrary monomials so the kernel checks the
    polynomial coefficient identity directly, without a symbolic ring tactic. -/
theorem gauss_bonnet_coeff_identity (AA AB BB : Int) :
    evaluate flattenedSquare AA AB BB =
      5 * evaluate ricciSquare AA AB BB + 24*AB := by
  rw [flattened_square_coeffs, ricci_square_coeffs]
  simp only [evaluate]
  omega

/-- The squared scalar curvature has coefficients (36,72,36). -/
theorem scalar_square_coeffs : weightedSquare 1 6 6 = ⟨36,72,36⟩ := by rfl

/-- The 2-form quadratic trace has coefficients (12,0,12), matching the
    standard Riemann-squared invariant in FLRW. -/
theorem bivector_square_coeffs :
    qAdd (weightedSquare 3 2 0) (weightedSquare 3 0 2) = ⟨12,0,12⟩ := by rfl

#print axioms form_degeneracies
#print axioms ricci_eigen_trace
#print axioms bivector_eigen_trace
#print axioms flattened_first_order
#print axioms flattened_square_coeffs
#print axioms ricci_square_coeffs
#print axioms gauss_bonnet_coeff_identity
#print axioms scalar_square_coeffs
#print axioms bivector_square_coeffs

end MathCan.TOEFLRW
