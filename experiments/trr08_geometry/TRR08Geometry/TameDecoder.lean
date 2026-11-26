module

public import TRR08Geometry.BlockPolynomial
public import TRR08Geometry.TameEigenvector
public import TRR08Geometry.ResidueMonomials

/-!
# An actual coordinate polynomial decoder gives the residue eigenvector

The assigned value at the identity contributes the negation permutation.
Finite monomial annihilation therefore turns a block-bounded coordinate
polynomial decoder into the original residue eigenvector equation.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve
open scoped BigOperators

variable {K : Type} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

/-- The coordinate function with the specified assigned value at the identity. -/
noncomputable def assignedX (u : K) (P : W.Point) : K := by
  classical
  exact if P = 0 then u else affineX P

/-- Equality with the assigned addition-coordinate table on nonidentity inputs. -/
def PolynomialDecoderOn (H : AddSubgroup W.Point) (u : K)
    (D : MvPolynomial (Fin 4) K) : Prop :=
  ∀ P Q : H, P ≠ 0 → Q ≠ 0 →
    blockEval D (affineX (P : W.Point)) (affineY (P : W.Point))
      (affineX (Q : W.Point)) (affineY (Q : W.Point)) =
        assignedX u ((P + Q : H) : W.Point)

omit [W.IsShortNF] in
theorem assignedX_add (H : AddSubgroup W.Point) (u : K) (P Q : H) :
    assignedX u ((P + Q : H) : W.Point) =
      affineX ((P + Q : H) : W.Point) + if Q = -P then u else 0 := by
  classical
  have hzero : ((P + Q : H) : W.Point) = 0 ↔ Q = -P := by
    constructor
    · intro h
      have hh : P + Q = 0 := Subtype.ext h
      exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hh)
    · rintro rfl
      simp
  unfold assignedX
  by_cases h : Q = -P
  · subst Q
    simp [affineX]
  · simp only [ite_eq_right (fun hz => h (hzero.mp hz)), ite_eq_right h, add_zero]

/-- The assigned identity value contributes exactly minus `u` times the residue. -/
theorem assignedX_residue_row (H : AddSubgroup W.Point) [Fintype H]
    (u : K) (P : H) :
    (∑ Q : H, subgroupResidue H Q * assignedX u ((P + Q : H) : W.Point)) =
      residueMatrixRow H P - u * subgroupResidue H P := by
  classical
  simp_rw [assignedX_add, mul_add]
  rw [Finset.sum_add_distrib]
  have hmain : (∑ Q : H,
      subgroupResidue H Q * affineX ((P + Q : H) : W.Point)) = residueMatrixRow H P := by
    unfold residueMatrixRow
    apply Finset.sum_congr rfl
    intro Q _
    ring
  rw [hmain]
  have hdelta : (∑ Q : H, subgroupResidue H Q * (if Q = -P then u else 0)) =
      -(u * subgroupResidue H P) := by
    simp [mul_ite, subgroupResidue_neg, mul_comm]
  rw [hdelta]
  ring

/-- Actual bounded polynomial rows give the eigenvector once their monomial
moments have been proved to vanish. -/
theorem polynomialDecoder_eigenvector_of_moments
    (H : AddSubgroup W.Point) [Fintype H] (d : ℕ) (u : K)
    (hmom : ∀ a b : ℕ, a + b ≤ d →
      ∑ Q : H, subgroupResidue H Q * affineX (Q : W.Point) ^ a *
        affineY (Q : W.Point) ^ b = 0)
    (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D)
    (hdecoder : PolynomialDecoderOn H u D) :
    ∀ P : H, P ≠ 0 → residueMatrixRow H P = u * subgroupResidue H P := by
  classical
  intro P hP
  have hs := sum_blockEval_right_eq_zero_of_moments
    (subgroupResidue H) (fun Q : H => affineX (Q : W.Point))
    (fun Q : H => affineY (Q : W.Point)) d hmom D hD
    (affineX (P : W.Point)) (affineY (P : W.Point))
  have he : (∑ Q : H, subgroupResidue H Q * assignedX u ((P + Q : H) : W.Point)) = 0 := by
    calc
      _ = ∑ Q : H, subgroupResidue H Q *
          blockEval D (affineX (P : W.Point)) (affineY (P : W.Point))
            (affineX (Q : W.Point)) (affineY (Q : W.Point)) := by
        apply Finset.sum_congr rfl
        intro Q _
        by_cases hQ : Q = 0
        · subst Q
          simp
        · rw [hdecoder P Q hP hQ]
      _ = 0 := hs
  rw [assignedX_residue_row] at he
  exact sub_eq_zero.mp he

/-- The coordinate degree bound itself supplies every residue moment. -/
theorem polynomialDecoder_residue_eigenvector
    (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0)
    (d : ℕ) (hdegree : 3 * d ≤ Fintype.card H - 1) (u : K)
    (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D)
    (hdecoder : PolynomialDecoderOn H u D) :
    ∀ P : H, P ≠ 0 → residueMatrixRow H P = u * subgroupResidue H P := by
  apply polynomialDecoder_eigenvector_of_moments H d u
    (sum_residue_ordinary_monomial_eq_zero H hno2 h₂ d hdegree) D hD hdecoder

/-- An actual ordinary block-degree decoder is impossible below the residue
threshold on a smooth short curve in tame odd marked order. -/
theorem tame_polynomialDecoder_exclusion [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hodd : Odd (addOrderOf T)) (hn : (addOrderOf T : K) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (d : ℕ) (hdegree : 3 * d ≤ addOrderOf T - 1) (u : K)
    (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D)
    (hdecoder : PolynomialDecoderOn (AddSubgroup.zmultiples T) u D) : False := by
  let := FiniteSlopeAverage.cyclicFintype T hfin
  have hd : 3 * d ≤ Fintype.card (AddSubgroup.zmultiples T) - 1 := by
    rw [FiniteSlopeAverage.cyclic_card T hfin]
    exact hdegree
  have he := polynomialDecoder_residue_eigenvector (AddSubgroup.zmultiples T)
    (cyclic_ne_neg_of_odd_order T hodd) h₂ d hd u D hD hdecoder
  exact tame_cyclicResidue_eigenvector_exclusion T hfin hT hodd hn h₂ h₃ u he

theorem tame_no_polynomialDecoder [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hodd : Odd (addOrderOf T)) (hn : (addOrderOf T : K) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (d : ℕ) (hdegree : 3 * d ≤ addOrderOf T - 1) (u : K) :
    ¬ ∃ D : MvPolynomial (Fin 4) K, BlockDegreeLE d D ∧
      PolynomialDecoderOn (AddSubgroup.zmultiples T) u D := by
  rintro ⟨D, hD, hdecoder⟩
  exact tame_polynomialDecoder_exclusion T hfin hT hodd hn h₂ h₃ d hdegree u D hD hdecoder

/-- Any coordinate decoder has block degree at least the ceiling of N/3. -/
theorem tame_polynomialDecoder_degree_lower_bound [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hodd : Odd (addOrderOf T)) (hn : (addOrderOf T : K) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (d : ℕ) (u : K) (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D)
    (hdecoder : PolynomialDecoderOn (AddSubgroup.zmultiples T) u D) :
    (addOrderOf T + 2) / 3 ≤ d := by
  by_contra h
  have hd : 3 * d ≤ addOrderOf T - 1 := by omega
  exact tame_polynomialDecoder_exclusion T hfin hT hodd hn h₂ h₃ d hd u D hD hdecoder

end TRR08Geometry

#print axioms TRR08Geometry.assignedX_add
#print axioms TRR08Geometry.assignedX_residue_row
#print axioms TRR08Geometry.polynomialDecoder_eigenvector_of_moments
#print axioms TRR08Geometry.polynomialDecoder_residue_eigenvector
#print axioms TRR08Geometry.tame_polynomialDecoder_exclusion
#print axioms TRR08Geometry.tame_no_polynomialDecoder
#print axioms TRR08Geometry.tame_polynomialDecoder_degree_lower_bound
