module

public import TRR08Geometry.DecoderDegree
public import TRR08Geometry.DecoderTransport
public import TRR08Geometry.ShortModelTransport

/-!
# Exact interpolation degree on a generalized Weierstrass model

The actual additive equivalence with a short model preserves marked order.
Affine substitution in both coordinate pairs and translation of the assigned
output transport the complete decoder existence statement.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type} [Field K] [DecidableEq K] {W : Affine K}

/-- The exact ordinary coordinate-block degree on any smooth Weierstrass
model in tame odd marked order at least nineteen. -/
theorem tame_general_polynomialDecoder_degree_iff [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hodd : Odd (addOrderOf T)) (hn : (addOrderOf T : K) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (d : ℕ) (u : K) :
    (∃ D : MvPolynomial (Fin 4) K,
      BlockDegreeLE d D ∧ PolynomialDecoderOn (AddSubgroup.zmultiples T) u D) ↔
        (addOrderOf T + 2) / 3 ≤ d := by
  let : Invertible (2 : K) := invertibleOfNonzero h₂
  let : Invertible (3 : K) := invertibleOfNonzero h₃
  let S := shearModel W W.toShortNF.r W.toShortNF.s W.toShortNF.t
  let e : S.Point ≃+ W.Point := shortPointEquiv W
  let Tₛ : S.Point := e.symm T
  have horder : addOrderOf Tₛ = addOrderOf T := e.symm.addOrderOf_eq T
  have hfinₛ : IsOfFinAddOrder Tₛ := e.symm.toAddMonoidHom.isOfFinAddOrder hfin
  have hTₛ : 19 ≤ addOrderOf Tₛ := by simpa only [horder] using hT
  have hoddₛ : Odd (addOrderOf Tₛ) := by simpa only [horder] using hodd
  have hnₛ : (addOrderOf Tₛ : K) ≠ 0 := by simpa only [horder] using hn
  have htransport := cyclic_polynomialDecoder_affine_iff e
    W.toShortNF.r W.toShortNF.s W.toShortNF.t
    (fun P hP => shortPointEquiv_x W hP)
    (fun P hP => shortPointEquiv_y W hP) Tₛ d (u-W.toShortNF.r)
  have hshort := tame_polynomialDecoder_degree_iff Tₛ hfinₛ hTₛ hoddₛ hnₛ
    h₂ h₃ d (u-W.toShortNF.r)
  have htarget : e Tₛ = T := e.apply_symm_apply T
  simpa only [htarget, sub_add_cancel, horder] using htransport.symm.trans hshort

theorem tame_general_polynomialDecoder_degree_lower_bound [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hodd : Odd (addOrderOf T)) (hn : (addOrderOf T : K) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (d : ℕ) (u : K) (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D)
    (hdecoder : PolynomialDecoderOn (AddSubgroup.zmultiples T) u D) :
    (addOrderOf T + 2) / 3 ≤ d :=
  (tame_general_polynomialDecoder_degree_iff T hfin hT hodd hn h₂ h₃ d u).mp
    ⟨D, hD, hdecoder⟩

theorem tame_general_polynomialDecoder_at_minimum [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hodd : Odd (addOrderOf T)) (hn : (addOrderOf T : K) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (u : K) :
    ∃ D : MvPolynomial (Fin 4) K,
      BlockDegreeLE ((addOrderOf T + 2) / 3) D ∧
      PolynomialDecoderOn (AddSubgroup.zmultiples T) u D :=
  (tame_general_polynomialDecoder_degree_iff T hfin hT hodd hn h₂ h₃
    ((addOrderOf T + 2) / 3) u).mpr le_rfl

end TRR08Geometry

#print axioms TRR08Geometry.tame_general_polynomialDecoder_degree_iff
#print axioms TRR08Geometry.tame_general_polynomialDecoder_degree_lower_bound
#print axioms TRR08Geometry.tame_general_polynomialDecoder_at_minimum
