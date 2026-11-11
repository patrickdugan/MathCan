import Init

/-!
# TOE-04: curvature traces of homogeneous isotropic GfE

The mathematical kernel checks scalar, vector and bivector multiplicities
and the four-dimensional FLRW quadratic Gauss-Bonnet identity. The analytic
logarithmic lapse equation and its numerical evolution remain separately
documented and tested in Python.
-/

namespace MathCan.TOEFLRW

theorem form_degeneracies : 1 + 1 + 3 + 3 + 3 = 11 := by omega

theorem ricci_eigen_trace (A B : Int) :
    3*A + 3*(A+2*B) = 6*(A+B) := by omega

theorem bivector_eigen_trace (A B : Int) :
    3*(2*A) + 3*(2*B) = 6*(A+B) := by omega

theorem flattened_first_order (A B : Int) :
    6*(A+B) + 3*A + 3*(A+2*B) + 3*(2*A) + 3*(2*B) =
    18*(A+B) := by omega

structure Quadratic where
  aa : Int
  ab : Int
  bb : Int
  deriving Repr, DecidableEq

def weightedSquare (w cA cB : Int) : Quadratic :=
  ⟨w*cA*cA, 2*w*cA*cB, w*cB*cB⟩

def qAdd (a b : Quadratic) : Quadratic :=
  ⟨a.aa + b.aa, a.ab + b.ab, a.bb + b.bb⟩

def flattenedSquare : Quadratic :=
  qAdd (weightedSquare 1 6 6)
    (qAdd (weightedSquare 1 3 0)
      (qAdd (weightedSquare 3 1 2)
        (qAdd (weightedSquare 3 2 0) (weightedSquare 3 0 2))))

def ricciSquare : Quadratic :=
  qAdd (weightedSquare 1 3 0) (weightedSquare 3 1 2)

theorem flattened_square_coeffs : flattenedSquare = ⟨60,84,60⟩ := by rfl

theorem ricci_square_coeffs : ricciSquare = ⟨12,12,12⟩ := by rfl

def evaluate (p : Quadratic) (AA AB BB : Int) : Int :=
  p.aa*AA + p.ab*AB + p.bb*BB

/-- On 4D FLRW, Tr(R_0² ⊕ R_1² ⊕ R_2²) = 5 Ricci² + GB,
    with Gauss-Bonnet density GB = 24 A B. -/
theorem gauss_bonnet_coeff_identity (AA AB BB : Int) :
    evaluate flattenedSquare AA AB BB =
      5 * evaluate ricciSquare AA AB BB + 24*AB := by
  rw [flattened_square_coeffs, ricci_square_coeffs]
  simp only [evaluate]
  omega

theorem scalar_square_coeffs :
    weightedSquare 1 6 6 = ⟨36,72,36⟩ := by rfl

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
