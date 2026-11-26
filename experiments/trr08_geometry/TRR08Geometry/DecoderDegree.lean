module

public import TRR08Geometry.BlockTensor
public import TRR08Geometry.PointInterpolation
public import TRR08Geometry.TameDecoder

/-!
# Exact ordinary block degree on a tame odd cyclic subgroup

Explicit bivariate point-mass interpolants construct the assigned coordinate
addition table as an actual four-variable polynomial. The resulting upper
bound and the residue exclusion give the exact degree threshold.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

/-- Ordinary point-mass polynomials construct the assigned addition-coordinate
decoder whenever the block bound reaches the subgroup order divided by three. -/
theorem exists_polynomialDecoder_of_card_le
    (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0)
    (d : ℕ) (hdegree : Fintype.card H ≤ 3 * d) (u : K) :
    ∃ D : MvPolynomial (Fin 4) K,
      BlockDegreeLE d D ∧ PolynomialDecoderOn H u D := by
  classical
  obtain ⟨L, hLdegree, hLeval⟩ := nonidentity_point_polynomial_family H hno2 h₂ hdegree
  let S := {P : H // P ≠ 0}
  let M : S → S → K := fun P Q => assignedX u ((P.val + Q.val : H) : W.Point)
  let D : MvPolynomial (Fin 4) K := matrixPolynomial M L
  refine ⟨D, matrixPolynomial_degree M L hLdegree, ?_⟩
  intro P Q hP hQ
  exact matrixPolynomial_eval M L
    (fun R : S => affineX (R.val : W.Point))
    (fun R : S => affineY (R.val : W.Point)) hLeval ⟨P, hP⟩ ⟨Q, hQ⟩

theorem exists_cyclic_polynomialDecoder
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hodd : Odd (addOrderOf T))
    (h₂ : (2 : K) ≠ 0) (d : ℕ) (hdegree : addOrderOf T ≤ 3 * d) (u : K) :
    ∃ D : MvPolynomial (Fin 4) K,
      BlockDegreeLE d D ∧ PolynomialDecoderOn (AddSubgroup.zmultiples T) u D := by
  let := FiniteSlopeAverage.cyclicFintype T hfin
  apply exists_polynomialDecoder_of_card_le (AddSubgroup.zmultiples T)
    (cyclic_ne_neg_of_odd_order T hodd) h₂ d ?_ u
  rwa [FiniteSlopeAverage.cyclic_card T hfin]

/-- The least ordinary degree in each coordinate pair is exactly ceil(N/3)
for every assigned identity value on a smooth short model in tame odd order. -/
theorem tame_polynomialDecoder_degree_iff [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hodd : Odd (addOrderOf T)) (hn : (addOrderOf T : K) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (d : ℕ) (u : K) :
    (∃ D : MvPolynomial (Fin 4) K,
      BlockDegreeLE d D ∧ PolynomialDecoderOn (AddSubgroup.zmultiples T) u D) ↔
        (addOrderOf T + 2) / 3 ≤ d := by
  constructor
  · rintro ⟨D, hD, hdecoder⟩
    exact tame_polynomialDecoder_degree_lower_bound T hfin hT hodd hn h₂ h₃ d u D hD hdecoder
  · intro hd
    apply exists_cyclic_polynomialDecoder T hfin hodd h₂ d ?_ u
    omega

end TRR08Geometry

#print axioms TRR08Geometry.exists_polynomialDecoder_of_card_le
#print axioms TRR08Geometry.exists_cyclic_polynomialDecoder
#print axioms TRR08Geometry.tame_polynomialDecoder_degree_iff
