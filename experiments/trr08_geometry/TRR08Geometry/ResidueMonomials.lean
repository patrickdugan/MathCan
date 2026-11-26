module

public import TRR08Geometry.ResidueAnnihilation
public import TRR08Geometry.CubicMonomials
public import TRR08Geometry.PolynomialDegree

/-!
# The actual residue functional annihilates bounded coordinate polynomials

Even y-powers cancel under inversion. Odd y-powers reduce to a univariate
polynomial whose degree is below the leading Lagrange coefficient. The
ordinary degree implication follows by comparing monomial weights.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

theorem residueSum_even_monomial (H : AddSubgroup W.Point) [Fintype H]
    (h₂ : (2 : K) ≠ 0) (a k : ℕ) :
    residueSum H (fun P => affineX (P : W.Point)^a * affineY (P : W.Point)^(2*k)) = 0 := by
  calc
    _ = residueSum H (fun P =>
        (cubicMonomial W.a₄ W.a₆ a k).eval (affineX (P : W.Point))) := by
      apply residueSum_congr_nonzero
      intro P hP
      exact even_monomial_on_curve (fun h => hP (Subtype.ext h)) a k
    _ = 0 := residueSum_xFunction H h₂ (fun x => (cubicMonomial W.a₄ W.a₆ a k).eval x)

theorem residueSum_odd_monomial (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) (a k : ℕ)
    (hweight : 2*a + 3*(2*k+1) ≤ Fintype.card H - 1) :
    residueSum H (fun P => affineX (P : W.Point)^a * affineY (P : W.Point)^(2*k+1)) = 0 := by
  have hc := subgroupXRoots_card H hno2
  have hnat : (cubicMonomial W.a₄ W.a₆ a k).natDegree < (subgroupXRoots H).card - 1 := by
    have hd := cubicMonomial_natDegree_le W.a₄ W.a₆ a k
    omega
  have hdegree : (cubicMonomial W.a₄ W.a₆ a k).degree <
      ((subgroupXRoots H).card - 1 : ℕ) := by
    apply lt_of_le_of_lt degree_le_natDegree
    exact_mod_cast hnat
  have hz := residueSum_normalForm_eq_zero H hno2 h₂ 0 (cubicMonomial W.a₄ W.a₆ a k) hdegree
  simp only [eval_zero, zero_add] at hz
  calc
    _ = residueSum H (fun P => affineY (P : W.Point) *
        (cubicMonomial W.a₄ W.a₆ a k).eval (affineX (P : W.Point))) := by
      apply residueSum_congr_nonzero
      intro P hP
      exact odd_monomial_on_curve (fun h => hP (Subtype.ext h)) a k
    _ = 0 := hz

/-- Actual residues annihilate every monomial below the subgroup pole threshold. -/
theorem residueSum_monomial_eq_zero (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) (a b : ℕ)
    (hweight : 2*a + 3*b ≤ Fintype.card H - 1) :
    residueSum H (fun P => affineX (P : W.Point)^a * affineY (P : W.Point)^b) = 0 := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' b
  · rw [hk]
    exact residueSum_even_monomial H h₂ a k
  · rw [hk] at hweight ⊢
    exact residueSum_odd_monomial H hno2 h₂ a k hweight

theorem sum_residue_monomial_eq_zero (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) (a b : ℕ)
    (hweight : 2*a + 3*b ≤ Fintype.card H - 1) :
    (∑ Q : H, subgroupResidue H Q * affineX (Q : W.Point)^a * affineY (Q : W.Point)^b) = 0 := by
  simpa only [residueSum, mul_assoc] using residueSum_monomial_eq_zero H hno2 h₂ a b hweight

theorem sum_residue_ordinary_monomial_eq_zero (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) (d : ℕ)
    (hdegree : 3*d ≤ Fintype.card H - 1) (a b : ℕ) (hab : a+b ≤ d) :
    (∑ Q : H, subgroupResidue H Q * affineX (Q : W.Point)^a * affineY (Q : W.Point)^b) = 0 := by
  exact sum_residue_monomial_eq_zero H hno2 h₂ a b (by omega)

/-- The concrete residue functional annihilates every actual bivariate
polynomial under the ordinary total-degree bound. -/
theorem residue_bivariateEval_eq_zero (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) (d : ℕ)
    (hdegree : 3*d ≤ Fintype.card H - 1)
    (F : MvPolynomial (Fin 2) K) (hF : F.totalDegree ≤ d) :
    (∑ Q : H, subgroupResidue H Q *
      bivariateEval F (affineX (Q : W.Point)) (affineY (Q : W.Point))) = 0 := by
  apply sum_bivariateEval_eq_zero_of_moments (subgroupResidue H)
    (fun Q => affineX (Q : W.Point)) (fun Q => affineY (Q : W.Point)) F hF
  exact sum_residue_ordinary_monomial_eq_zero H hno2 h₂ d hdegree

end TRR08Geometry

#print axioms TRR08Geometry.residueSum_even_monomial
#print axioms TRR08Geometry.residueSum_odd_monomial
#print axioms TRR08Geometry.residueSum_monomial_eq_zero
#print axioms TRR08Geometry.sum_residue_monomial_eq_zero
#print axioms TRR08Geometry.sum_residue_ordinary_monomial_eq_zero
#print axioms TRR08Geometry.residue_bivariateEval_eq_zero
