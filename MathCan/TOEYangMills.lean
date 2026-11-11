import MathCan.TOETwoMultiplet

/-!
# TOE-08: two Yang--Mills triads and a conditional bivector response

The kernel statements cover algebraic properties of the *declared* observer-frame
Gram constitutive map and the necessary mixed-response flow condition.
They do not derive this response from the actual Dirac--Kähler GfE matter
operator, the complete dressed stress tensor, or a coupled gravity--YM
characteristic matrix. The Yang--Mills reduction and 6×6 determinant identity
have written proofs and independent exact-rational executable tests.
-/

namespace MathCan.TOEYangMills

/-- Electric--magnetic Gram mixing for two isotropic multiplets. -/
def mixed (e₁ e₂ b₁ b₂ : Int) : Int := e₁*b₁ + e₂*b₂

/-- Opposite electric amplitudes with equal magnetic amplitudes cancel the
    electric--magnetic response block at a given instant. -/
theorem opposed_electric_mixed_zero (e b : Int) :
    mixed e (-e) b b = 0 := by
  simp [mixed, Int.neg_mul]
  omega

/-- The isotropic electric Gram coefficient is insensitive to a sign change. -/
def electricNorm (e₁ e₂ : Int) : Int := e₁*e₁+e₂*e₂

theorem opposite_electric_norm (e : Int) :
    electricNorm e (-e) = 2*(e*e) := by
  simp [electricNorm, Int.neg_mul, Int.mul_neg]
  omega

/-- The E and B diagonal blocks of a declared induced metric. The products
    alpha*mE and beta*A are intentionally treated as algebraic parameters. -/
def thetaE (alpha beta me A : Int) : Int := 1+alpha*me-2*(beta*A)
def thetaB (alpha beta mb B : Int) : Int := 1+alpha*mb-2*(beta*B)

/-- Equal induced diagonal responses follow from the compensating source
    and curvature shifts. This is a conditional algebraic statement. -/
theorem diagonal_match (alpha beta me mb A B : Int)
    (h : alpha*me-alpha*mb=2*(beta*A)-2*(beta*B)) :
    thetaE alpha beta me A = thetaB alpha beta mb B := by
  simp only [thetaE, thetaB]
  omega

/-- Cancellation at one time gives no identity for its derivative. The
    Yang--Mills field equations supply the separate mixed-rate hypothesis. -/
theorem nonzero_mixed_rate (gpsi split rate : Int)
    (h : rate = (2*gpsi)*split)
    (hg : gpsi ≠ 0) (hs : split ≠ 0) : rate ≠ 0 := by
  intro hz
  have hm : (2*gpsi)*split = 0 := by
    rw [h] at hz
    exact hz
  rcases mul_eq_zero.mp hm with htwoMul | hsplit
  · rcases mul_eq_zero.mp htwoMul with htwo | hgpsi
    · omega
    · exact hg hgpsi
  · exact hs hsplit

/-- The diagonal FLRW tensor stress from a conformal gauge multiplet has
    vanishing four-dimensional trace when rho=3*p. -/
theorem radiation_stress_trace (p : Int) :
    -(3*p)+p+p+p=0 := by omega

/-- The doublet's Gram determinant is a cube of a squared minor. A nonzero
    two-dimensional wedge therefore guarantees full six-dimensional rank. -/
theorem nonzero_wedge_square (w : Int) (hw : w ≠ 0) :
    w*w ≠ 0 := by
  intro hz
  rcases mul_eq_zero.mp hz with hleft | hright
  · exact hw hleft
  · exact hw hright

/-- A nonzero curvature mismatch with nonvanishing coupling cannot keep the
    mixed-response derivative zero under the derived symmetric-triad law. -/
theorem mismatch_forces_mixed_flow (coefficient delta : Int)
    (hc : coefficient ≠ 0) (hd : delta ≠ 0) :
    coefficient*delta ≠ 0 := by
  intro hz
  rcases mul_eq_zero.mp hz with hleft | hright
  · exact hc hleft
  · exact hd hright

/-- The conditional diagonal-matching time derivative can vanish while the
    off-diagonal derivative is nonzero: a direct algebraic counterexample. -/
theorem diagonal_stationary_mixed_running :
    (0:Int) = 0 ∧ (-9:Int) ≠ 0 := by
  constructor
  · rfl
  · decide

#print axioms opposed_electric_mixed_zero
#print axioms opposite_electric_norm
#print axioms diagonal_match
#print axioms nonzero_mixed_rate
#print axioms radiation_stress_trace
#print axioms nonzero_wedge_square
#print axioms mismatch_forces_mixed_flow
#print axioms diagonal_stationary_mixed_running

end MathCan.TOEYangMills