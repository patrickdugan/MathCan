import Init

/-!
# TOE-03: exact FRW nuisance-mode absorption

These integer identities express a structural identifiability obstruction for
an explicitly declared four-column Friedmann *proxy*. The source discussion
of GfE involves additional G-field derivatives and dressed curvature.
Neither the physical field equations nor the covariance Schur-complement
identity is formalized by this module.
-/
namespace MathCan.TOECosmology

/-- The unnormalized four-mode Friedmann template as a polynomial in x=1+z. -/
def background (x lambda curvature matter radiation : Int) : Int :=
  lambda + curvature * x^2 + matter * x^3 + radiation * x^4

/-- A redshift mode that vanishes at present (x=1). -/
def anchored (x : Int) (power : Nat) : Int := x^power - 1

theorem anchored_present (power : Nat) : anchored 1 power = 0 := by
  simp [anchored]

/-- A quadratic-in-x perturbation can be absorbed into curvature and lambda. -/
theorem curvature_mode_absorbed
    (x lambda curvature matter radiation epsilon : Int) :
    background x (lambda - epsilon) (curvature + epsilon) matter radiation =
      background x lambda curvature matter radiation + epsilon * anchored x 2 := by
  simp only [background, anchored, add_mul, sub_mul, mul_sub]
  omega

/-- A cubic-in-x perturbation can be absorbed into matter and lambda. -/
theorem matter_mode_absorbed
    (x lambda curvature matter radiation epsilon : Int) :
    background x (lambda - epsilon) curvature (matter + epsilon) radiation =
      background x lambda curvature matter radiation + epsilon * anchored x 3 := by
  simp only [background, anchored, add_mul, sub_mul, mul_sub]
  omega

/-- A quartic-in-x perturbation can be absorbed into radiation and lambda. -/
theorem radiation_mode_absorbed
    (x lambda curvature matter radiation epsilon : Int) :
    background x (lambda - epsilon) curvature matter (radiation + epsilon) =
      background x lambda curvature matter radiation + epsilon * anchored x 4 := by
  simp only [background, anchored, add_mul, sub_mul, mul_sub]
  omega

/-- The present-day value of the background is the coefficient sum. -/
theorem background_present
    (lambda curvature matter radiation : Int) :
    background 1 lambda curvature matter radiation =
      lambda + curvature + matter + radiation := by
  simp [background]

/-- A source-aligned quadratic mode can be absorbed whenever its polynomial
    expansion is supplied as an independently verified identity. -/
theorem conditional_quadratic_blind_mode
    (x lambda curvature matter radiation epsilon quadratic : Int)
    (shape : quadratic = 1 - 2*x^2 + x^4) :
    background x (lambda + epsilon) (curvature - 2*epsilon)
      matter (radiation + epsilon) =
      background x lambda curvature matter radiation + epsilon * quadratic := by
  rw [shape]
  simp only [background, add_mul, sub_mul, mul_sub]
  omega

#print axioms anchored_present
#print axioms curvature_mode_absorbed
#print axioms matter_mode_absorbed
#print axioms radiation_mode_absorbed
#print axioms background_present
#print axioms conditional_quadratic_blind_mode

end MathCan.TOECosmology
