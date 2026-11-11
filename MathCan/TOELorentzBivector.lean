import Init

/-!
# TOE-09: Lorentzian bivector signature and conditional eigenvalue obstruction

Bianconi's 2025 Appendix A gives an Abelian gauge F⊗F metric, and Appendix B
sets the bivector eigenproblem by raising a bivector pair with g_(2).
For signature (-+++), the raised 2-form metric has signs (-,-,-,+,+,+).

These kernel-checked lemmas concern the INTEGER algebra of a declared
isotropic two-flavor extension of that operator. In particular, the source
GfE action, non-Abelian matter equations and full graviton principal symbol
are separate physical obligations. Purely polynomial six-dimensional
identities are tested by an independent exact rational Python oracle.
-/

namespace MathCan.TOELorentzBivector

/-- Electric gauge Gram response enters with the Lorentzian minus sign. -/
def thetaE (electric curvatureE : Int) : Int := 1-electric-curvatureE

/-- Magnetic gauge Gram response enters with the Lorentzian plus sign. -/
def thetaB (magnetic curvatureB : Int) : Int := 1+magnetic-curvatureB

/-- Equating the two diagonal blocks fixes the SUM of electric and magnetic
    source magnitudes relative to the curvature gap. -/
theorem diagonal_matching_iff
    (electric magnetic curvatureE curvatureB : Int) :
    thetaE electric curvatureE = thetaB magnetic curvatureB ↔
    electric + magnetic = curvatureB-curvatureE := by
  simp only [thetaE, thetaB]
  omega

/-- The diagonal response gap includes both positive Gram magnitudes. -/
theorem source_gap_identity
    (electric magnetic curvatureE curvatureB : Int) :
    thetaE electric curvatureE - thetaB magnetic curvatureB =
    -(electric+magnetic) - (curvatureE-curvatureB) := by
  simp only [thetaE, thetaB]
  omega

/-- With electric and magnetic matching, a nonzero off-diagonal response
    produces a negative two-by-two characteristic discriminant. -/
def blockDiscriminant (gap mixing : Int) : Int :=
  gap*gap-4*(mixing*mixing)

theorem matched_discriminant (mixing : Int) :
    blockDiscriminant 0 mixing = -(4*(mixing*mixing)) := by
  simp [blockDiscriminant]

theorem negative_discriminant_of_positive_mixed_square (mixing : Int)
    (hPositive : 0 < mixing*mixing) :
    blockDiscriminant 0 mixing < 0 := by
  rw [matched_discriminant]
  omega

/-- If the aligned diagonal block has a nonnegative real-root
    discriminant, its mixed response must vanish. The square's
    nonnegativity follows from integer arithmetic in the intended model. -/
theorem matched_real_spectrum_forces_zero_mixing (mixing : Int)
    (hNonnegative : 0 ≤ mixing*mixing)
    (realSpectrum : 0 ≤ blockDiscriminant 0 mixing) :
    mixing = 0 := by
  rw [matched_discriminant] at realSpectrum
  have hsquare : mixing*mixing=0 := by omega
  rcases Int.mul_eq_zero.mp hsquare with hz | hz
  · exact hz
  · exact hz

/-- Covariant Gram determinant for a single flavor-direction pair. -/
def gramDet (electric magnetic mixed : Int) : Int :=
  electric*magnetic-mixed*mixed

/-- Raising the second bivector index changes its two-dimensional determinant
    sign: the electric and magnetic Lorentzian signs are opposite. -/
def raisedDet (electric magnetic mixed : Int) : Int :=
  (-electric)*magnetic+mixed*mixed

theorem raised_det_sign_flip (electric magnetic mixed : Int) :
    raisedDet electric magnetic mixed = -gramDet electric magnetic mixed := by
  simp only [raisedDet, gramDet, Int.neg_mul]
  omega

/-- The two-flavor Gram relation transports to the raised-index operator. -/
theorem raised_det_flavor_area (electric magnetic mixed wedge : Int)
    (lagrange : electric*magnetic-mixed*mixed=wedge*wedge) :
    raisedDet electric magnetic mixed=-(wedge*wedge) := by
  have hgram : gramDet electric magnetic mixed = wedge*wedge := by
    simpa only [gramDet] using lagrange
  rw [raised_det_sign_flip, hgram]

/-- A nonzero flavor-area determinant remains nonzero after signature raising. -/
theorem nonzero_raised_determinant (electric magnetic mixed wedge : Int)
    (lagrange : electric*magnetic-mixed*mixed=wedge*wedge)
    (wedgeNonzero : wedge ≠ 0) :
    raisedDet electric magnetic mixed ≠ 0 := by
  rw [raised_det_flavor_area electric magnetic mixed wedge lagrange]
  intro hz
  have hs : wedge*wedge=0 := by omega
  rcases Int.mul_eq_zero.mp hs with hw | hw
  · exact wedgeNonzero hw
  · exact wedgeNonzero hw

/-- Exact scalar condition for loss of a real characteristic spectrum. -/
theorem complex_pair_of_offdiag_dominance
    (gap squareMix : Int) (hSquare : 0 ≤ squareMix)
    (domination : gap*gap < 4*squareMix) :
    gap*gap-4*squareMix < 0 := by omega

#print axioms diagonal_matching_iff
#print axioms source_gap_identity
#print axioms matched_discriminant
#print axioms negative_discriminant_of_positive_mixed_square
#print axioms matched_real_spectrum_forces_zero_mixing
#print axioms raised_det_sign_flip
#print axioms raised_det_flavor_area
#print axioms nonzero_raised_determinant
#print axioms complex_pair_of_offdiag_dominance

end MathCan.TOELorentzBivector
