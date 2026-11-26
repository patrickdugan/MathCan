module

public import TRR08Geometry.PolynomialLift
public import TRR08Geometry.ResidueEigenvector
public import TRR08Geometry.RootCardinality

/-!
# Explicit point-mass interpolators on the nonidentity subgroup

The x-coordinate Lagrange basis isolates an inverse pair. The factor
`(y+y(P))/(2*y(P))` selects its marked member. The ordinary-degree lift
turns this normal form into an actual bivariate polynomial.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

noncomputable def subgroupPointInterpolator (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : MvPolynomial (Fin 2) K :=
  normalFormLift W.a₄ W.a₆
    (Polynomial.C (1 / 2) * Lagrange.basis (subgroupXRoots H) id (affineX (P : W.Point)))
    (Polynomial.C (1 / (2 * affineY (P : W.Point))) *
      Lagrange.basis (subgroupXRoots H) id (affineX (P : W.Point)))

/-- The constructed ordinary polynomial is the point mass on nonidentity points. -/
theorem subgroupPointInterpolator_eval (H : AddSubgroup W.Point) [Fintype H]
    (P Q : H) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hno2 : ∀ R : H, R ≠ 0 → R ≠ -R) (h₂ : (2 : K) ≠ 0) :
    bivariateEval (subgroupPointInterpolator H P)
      (affineX (Q : W.Point)) (affineY (Q : W.Point)) = if Q = P then 1 else 0 := by
  classical
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hq : (Q : W.Point) ≠ 0 := fun h => hQ (Subtype.ext h)
  have hd : (P : W.Point) + (P : W.Point) ≠ 0 := by
    intro hz
    exact hno2 P hP (eq_neg_iff_add_eq_zero.mpr (Subtype.ext hz))
  have hy := short_y_ne_zero hp hd
  have hProot := subgroupXRoots_mem H P hP
  have hQroot := subgroupXRoots_mem H Q hQ
  have hinj : Set.InjOn (id : K → K) (subgroupXRoots H) := fun _ _ _ _ h => h
  unfold subgroupPointInterpolator
  rw [normalFormLift_eval W.a₄ W.a₆ _ _ (short_curve_equation hq)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  by_cases hx : affineX (Q : W.Point) = affineX (P : W.Point)
  · have hb : (Lagrange.basis (subgroupXRoots H) id (affineX (P : W.Point))).eval
        (affineX (Q : W.Point)) = 1 := by
      rw [hx]
      exact Lagrange.eval_basis_self hinj hProot
    rw [hb]
    simp only [mul_one]
    rcases (affineX_eq_iff hq hp).mp hx with he | he
    · have hQP : Q = P := Subtype.ext he
      subst Q
      simp only [ite_true]
      field_simp [h₂, hy]
      ring
    · have hQP : Q = -P := Subtype.ext he
      rw [hQP, ite_eq_right (Ne.symm (hno2 P hP))]
      simp only [AddSubgroup.coe_neg, affineY_neg]
      field_simp [h₂, hy]
      ring
  · have hb : (Lagrange.basis (subgroupXRoots H) id (affineX (P : W.Point))).eval
        (affineX (Q : W.Point)) = 0 :=
      Lagrange.eval_basis_of_ne (v := id) (Ne.symm hx) hQroot
    have hQP : Q ≠ P := by
      intro he
      exact hx (congrArg (fun R : H => affineX (R : W.Point)) he)
    rw [hb]
    simp [hQP]

/-- A bound in terms of the number of distinct x-roots. -/
theorem subgroupPointInterpolator_totalDegree_le_roots
    (H : AddSubgroup W.Point) [Fintype H] (P : H) (hP : P ≠ 0) {d : ℕ}
    (hd : 2 * (subgroupXRoots H).card + 1 ≤ 3 * d) :
    (subgroupPointInterpolator H P).totalDegree ≤ d := by
  have hProot := subgroupXRoots_mem H P hP
  have hinj : Set.InjOn (id : K → K) (subgroupXRoots H) := fun _ _ _ _ h => h
  have hm : 0 < (subgroupXRoots H).card := Finset.card_pos.mpr ⟨_, hProot⟩
  have hb := Lagrange.natDegree_basis hinj hProot
  have hscalar (c : K) :
      (Polynomial.C c * Lagrange.basis (subgroupXRoots H) id (affineX (P : W.Point))).natDegree ≤
        (subgroupXRoots H).card - 1 := by
    calc
      _ ≤ (Polynomial.C c : Polynomial K).natDegree +
          (Lagrange.basis (subgroupXRoots H) id (affineX (P : W.Point))).natDegree :=
        Polynomial.natDegree_mul_le
      _ = _ := by rw [Polynomial.natDegree_C, zero_add, hb]
  unfold subgroupPointInterpolator
  apply normalFormLift_totalDegree_le
  · have h := hscalar (1 / 2)
    omega
  · have h := hscalar (1 / (2 * affineY (P : W.Point)))
    omega

/-- Point masses have the advertised ordinary degree in terms of the subgroup order. -/
theorem subgroupPointInterpolator_totalDegree_le
    (H : AddSubgroup W.Point) [Fintype H] (P : H) (hP : P ≠ 0)
    (hno2 : ∀ R : H, R ≠ 0 → R ≠ -R) {d : ℕ} (hd : Fintype.card H ≤ 3 * d) :
    (subgroupPointInterpolator H P).totalDegree ≤ d := by
  apply subgroupPointInterpolator_totalDegree_le_roots H P hP
  rwa [subgroupXRoots_card H hno2]

/-- The explicit polynomial family supplies point masses on the nonidentity subtype. -/
theorem nonidentity_point_polynomial_family (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ R : H, R ≠ 0 → R ≠ -R) (h₂ : (2 : K) ≠ 0)
    {d : ℕ} (hd : Fintype.card H ≤ 3 * d) :
    ∃ L : {P : H // P ≠ 0} → MvPolynomial (Fin 2) K,
      (∀ P, (L P).totalDegree ≤ d) ∧
      ∀ P Q, bivariateEval (L P) (affineX (Q.val : W.Point))
        (affineY (Q.val : W.Point)) = if Q = P then 1 else 0 := by
  classical
  refine ⟨fun P => subgroupPointInterpolator H P.val, ?_, ?_⟩
  · intro P
    exact subgroupPointInterpolator_totalDegree_le H P.val P.property hno2 hd
  · intro P Q
    rw [subgroupPointInterpolator_eval H P.val Q.val P.property Q.property hno2 h₂]
    simp only [Subtype.val_inj]

end TRR08Geometry

#print axioms TRR08Geometry.subgroupPointInterpolator_eval
#print axioms TRR08Geometry.subgroupPointInterpolator_totalDegree_le_roots
#print axioms TRR08Geometry.subgroupPointInterpolator_totalDegree_le
#print axioms TRR08Geometry.nonidentity_point_polynomial_family
