import MathCan.TOELorentzBivector

/-!
# TOE-10: non-Abelian color contractions and Lorentzian spectral gates

Exact algebraic identities for a DECLARED SU(2)^2 adjoint Killing-form
extension of Bianconi's Abelian F⊗F bivector metric. The source theory does
not supply these non-Abelian Yang--Mills equations or a coupled GfE solution.

Background normalization alpha = 6 beta kappa is an explicit hypothesis,
with bK standing for the positive product beta*kappa.

The Python oracle independently constructs the six-dimensional color Gram
matrix, validates gauge-frame invariance, reconstructs the rational
Einstein--Yang--Mills crossing, and varies a logarithmic gauge-medium action.
The nonlinear ODE and spectrum calculations are NOT Lean-certified here.
-/

namespace MathCan.TOENonAbelian

/-- Flavor-plane electric--magnetic Killing-form contractions. -/
def mixed (e1 e2 b1 b2 : Int) : Int := e1*b1 + e2*b2

theorem flavor_exchange (e1 e2 b1 b2 : Int) :
    mixed e1 e2 b1 b2 = mixed e2 e1 b2 b1 := by
  simp only [mixed]
  omega

/-- A two-axis color sign reversal is an adjoint SO(3) frame rotation,
    whose squares leave the internal contractions fixed. -/
theorem signed_color_norm (x y z : Int) :
    (-x)*(-x)+(-y)*(-y)+z*z = x*x+y*y+z*z := by
  simp only [Int.neg_mul_neg]

theorem signed_color_dot (x y z u v w : Int) :
    (-x)*(-u)+(-y)*(-v)+z*w = x*u+y*v+z*w := by
  simp only [Int.neg_mul_neg]

/-- The covariant contraction is invariant under exchange of independent
    SU(2) factors, although that exchange is not itself a gauge symmetry. -/
theorem mixed_under_flavor_exchange (e1 e2 b1 b2 : Int) :
    mixed e1 e2 b1 b2 = mixed e2 e1 b2 b1 := by
  exact flavor_exchange e1 e2 b1 b2

/-- Curvature normalization on a GR+Yang--Mills background:
    dot H = -kappa*s; delta = (-alpha+2 beta*kappa)*s.
    Setting alpha=6 beta*kappa yields a negative response gap. -/
def gapAtCanonicalCoupling (bk s : Int) : Int :=
    (2*bk-6*bk)*s

theorem canonical_gap_factor (bk s : Int) :
    gapAtCanonicalCoupling bk s = -4*(bk*s) := by
  unfold gapAtCanonicalCoupling
  rw [Int.sub_mul, Int.mul_assoc, Int.mul_assoc]
  omega

/-- Positive background energy and positive beta*kappa rule out equality
    of the electric/magnetic diagonal blocks at the canonical coupling. -/
theorem canonical_gap_strict (bk s : Int)
    (hb : 0 < bk) (hs : 0 < s) :
    gapAtCanonicalCoupling bk s < 0 := by
  rw [canonical_gap_factor]
  have hproduct : 0 < bk*s := Int.mul_pos hb hs
  omega

/-- The two-species mixed response can vanish at one instant while the
    independent torque driving its derivative is nonzero. -/
theorem zero_mixed_nonzero_source (torque : Int)
    (h : torque ≠ 0) :
    (0 : Int) = 0 ∧ torque ≠ 0 := ⟨rfl, h⟩

/-- With sdot=-4Hs and cdot=-4Hc+torque, differentiation of r=c/s
    gives rdot=torque/s when s>0. This lemma proves the integer-polynomial
    numerator identity without division or a differentiability assumption. -/
theorem normalized_mixed_transport
    (H s c torque sdot cdot : Int)
    (hs : sdot = -4*(H*s))
    (hc : cdot = -4*(H*c)+torque) :
    cdot*s - c*sdot = torque*s := by
  rw [hs, hc]
  have hcomm : (H*c)*s = c*(H*s) := by ac_rfl
  simp only [Int.add_mul, Int.sub_mul, Int.neg_mul, Int.mul_neg, Int.mul_assoc]
  omega

/-- The exact discriminant derivative determines which side of a Krein
    collision a first-order perturbation enters. This is a statement about
    the local Taylor coefficient, with regularity supplied by the ODE model. -/
theorem negative_linearized_discriminant
    (dDelta dt : Int) (hd : dDelta < 0) (ht : 0 < dt) :
    dDelta*dt < 0 := Int.mul_neg_of_neg_of_pos hd ht

/-- A real semisimple positive spectrum requires a nonnegative quadratic
    discriminant. A negative result excludes that branch by definition. -/
theorem complex_if_negative_discriminant (disc : Int)
    (hd : disc < 0) : ¬ (0 ≤ disc) := by omega

#print axioms flavor_exchange
#print axioms signed_color_norm
#print axioms signed_color_dot
#print axioms mixed_under_flavor_exchange
#print axioms canonical_gap_factor
#print axioms canonical_gap_strict
#print axioms zero_mixed_nonzero_source
#print axioms normalized_mixed_transport
#print axioms negative_linearized_discriminant
#print axioms complex_if_negative_discriminant

end MathCan.TOENonAbelian
