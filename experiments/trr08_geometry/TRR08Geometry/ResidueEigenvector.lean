module

public import TRR08Geometry.TraceCoefficient
public import TRR08Geometry.BarycentricResidue

/-!
# A residue eigenvector gives the actual second local coefficient

The matrix row is evaluated on actual subgroup points, with x(O) = 0.
The residue weights are the original inverse tangent-times-root-product
weights. Inversion pairs its summands, and the finite barycentric identity
identifies the resulting weighted reciprocal sum.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve
open scoped BigOperators

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

noncomputable def subgroupNodalWeight (H : AddSubgroup W.Point) [Fintype H]
    (v : K) : K := Lagrange.nodalWeight (subgroupXRoots H) id v

noncomputable def subgroupResidue (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : K := subgroupNodalWeight H (affineX (P : W.Point)) /
      (2 * affineY (P : W.Point))

noncomputable def residueMatrixRow (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : K := ∑ Q : H,
      affineX ((P + Q : H) : W.Point) * subgroupResidue H Q

theorem subgroupXRoots_mem (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) : affineX (P : W.Point) ∈ subgroupXRoots H := by
  classical
  exact Finset.mem_image.mpr ⟨P, by simp [hP], rfl⟩

@[simp] theorem subgroupResidue_zero (H : AddSubgroup W.Point) [Fintype H] :
    subgroupResidue H 0 = 0 := by
  simp [subgroupResidue, affineY]

@[simp] theorem subgroupResidue_neg (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : subgroupResidue H (-P) = -subgroupResidue H P := by
  simp [subgroupResidue, div_neg_eq_neg_div]

theorem subgroupResidue_eq_inverse_product (H : AddSubgroup W.Point) [Fintype H]
    (P : H) : subgroupResidue H P =
      1 / (2 * affineY (P : W.Point) *
        ∏ v ∈ (subgroupXRoots H).erase (affineX (P : W.Point)),
          (affineX (P : W.Point) - v)) := by
  simp [subgroupResidue, subgroupNodalWeight, Lagrange.nodalWeight,
    div_eq_mul_inv, Finset.prod_inv_distrib]

theorem subgroupResidue_ne_zero (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hdouble : P + P ≠ 0) (h₂ : (2 : K) ≠ 0) :
    subgroupResidue H P ≠ 0 := by
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hd : (P : W.Point) + (P : W.Point) ≠ 0 := fun h => hdouble (Subtype.ext h)
  apply div_ne_zero
  · exact Lagrange.nodalWeight_ne_zero (fun _ _ _ _ h => h) (subgroupXRoots_mem H P hP)
  · exact mul_ne_zero h₂ (short_y_ne_zero hp hd)

/-- The difference of paired x-coordinates comes from the actual addition law. -/
theorem paired_add_x_difference {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : affineX P ≠ affineX Q) :
    affineX (P + Q) - affineX (P - Q) =
      -(4 * affineY P * affineY Q) / (affineX P - affineX Q)^2 := by
  have hadd : P + Q ≠ 0 := by
    intro h
    have he : P = -Q := eq_neg_iff_add_eq_zero.mpr h
    exact hx (by rw [he, affineX_neg])
  have hsub : P + -Q ≠ 0 := by
    intro h
    have he : P = Q := by simpa using (eq_neg_iff_add_eq_zero.mpr h)
    exact hx (congrArg affineX he)
  change affineX (P + Q) - affineX (P + -Q) = _
  rw [normalizedSlope_add_x hP hQ hadd,
    normalizedSlope_add_x hP (neg_ne_zero.mpr hQ) hsub,
    normalizedSlope_of_x_ne hP hQ hx,
    normalizedSlope_of_x_ne hP (neg_ne_zero.mpr hQ) (by simpa using hx)]
  simp only [affineX_neg, affineY_neg, sub_neg_eq_add]
  have hd := sub_ne_zero.mpr hx
  field_simp
  ring

/-- Pairing the actual summands cancels the y-coordinate of the second point. -/
theorem residue_summand_pair (H : AddSubgroup W.Point) [Fintype H]
    (P Q : H) (hP : P ≠ 0) (hQ : Q ∈ coefficientOthers H P)
    (hno2 : ∀ R : H, R ≠ 0 → R ≠ -R) (h₂ : (2 : K) ≠ 0) :
    affineX ((P + Q : H) : W.Point) * subgroupResidue H Q +
      affineX ((P + -Q : H) : W.Point) * subgroupResidue H (-Q) =
      -(2 * affineY (P : W.Point)) *
        (subgroupNodalWeight H (affineX (Q : W.Point)) /
          (affineX (P : W.Point) - affineX (Q : W.Point))^2) := by
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hQ0 := (mem_coefficientOthers.mp hQ).1
  have hq : (Q : W.Point) ≠ 0 := fun h => hQ0 (Subtype.ext h)
  have hqd : (Q : W.Point) + (Q : W.Point) ≠ 0 := by
    intro h
    exact hno2 Q hQ0 (eq_neg_iff_add_eq_zero.mpr (Subtype.ext h))
  have hy := short_y_ne_zero hq hqd
  have hx := coefficientOthers_x_ne hP hQ
  rw [subgroupResidue_neg]
  rw [mul_neg, ← sub_eq_add_neg, ← sub_mul]
  change (affineX ((P : W.Point) + (Q : W.Point)) -
    affineX ((P : W.Point) - (Q : W.Point))) * subgroupResidue H Q = _
  rw [paired_add_x_difference hp hq hx]
  unfold subgroupResidue
  field_simp
  ring

/-- The complete matrix row after inversion pairing and passing to distinct x-roots. -/
theorem residueMatrixRow_by_roots (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q)
    (h₂ : (2 : K) ≠ 0) :
    residueMatrixRow H P =
      affineX (((P + P : H)) : W.Point) * subgroupResidue H P -
      2 * affineY (P : W.Point) *
        ∑ v ∈ (subgroupXRoots H).erase (affineX (P : W.Point)),
          subgroupNodalWeight H v / (affineX (P : W.Point) - v)^2 := by
  classical
  have hd : P + P ≠ 0 := fun h => hno2 P hP (eq_neg_iff_add_eq_zero.mpr h)
  let f : H → K := fun Q => affineX ((P + Q : H) : W.Point) * subgroupResidue H Q
  let g : K → K := fun v => subgroupNodalWeight H v / (affineX (P : W.Point) - v)^2
  have hi := coefficientOthers_neg_sum H P f
  have hp : 2 * (∑ Q ∈ coefficientOthers H P, f Q) =
      -(2 * affineY (P : W.Point)) *
        (∑ Q ∈ coefficientOthers H P, g (affineX (Q : W.Point))) := by
    calc
      2 * (∑ Q ∈ coefficientOthers H P, f Q) =
          (∑ Q ∈ coefficientOthers H P, f Q) + ∑ Q ∈ coefficientOthers H P, f (-Q) := by
        rw [hi]
        ring
      _ = ∑ Q ∈ coefficientOthers H P, (f Q + f (-Q)) := (Finset.sum_add_distrib).symm
      _ = ∑ Q ∈ coefficientOthers H P,
          -(2 * affineY (P : W.Point)) * g (affineX (Q : W.Point)) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        exact residue_summand_pair H P Q hP hQ hno2 h₂
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [coefficientOthers_sum_by_roots H P hP hno2 g] at hp
  have hs : (∑ Q ∈ coefficientOthers H P, f Q) =
      -(2 * affineY (P : W.Point)) *
        (∑ v ∈ (subgroupXRoots H).erase (affineX (P : W.Point)), g v) := by
    apply mul_left_cancel₀ h₂
    linear_combination hp
  unfold residueMatrixRow
  rw [coefficient_sum_split H P hP hd]
  simp only [subgroupResidue_zero, mul_zero, add_zero, add_neg_cancel,
    AddSubgroup.coe_zero, show affineX (0 : W.Point) = 0 by rfl, zero_mul, zero_add]
  change _ + ∑ Q ∈ coefficientOthers H P, f Q = _
  rw [hs]
  dsimp [g]
  ring


private theorem residue_coefficient_algebra (m x y D U S Q : K)
    (h₂ : (2 : K) ≠ 0) (hy : y ≠ 0) (hD : D ≠ 0)
    (hr : 2 * D * U = -(S^2 + Q)) :
    (m^2 - 2*x) * (D⁻¹ / (2*y)) - 2*y*U =
      (m^2 - 2*x + (y^2/2)*(2*S)^2 + y^2*(2*Q)) * (D⁻¹ / (2*y)) := by
  field_simp
  linear_combination -2 * y^2 * hr

/-- The original residue matrix row is the second local coefficient times its residue. -/
theorem residueMatrixRow_eq_localSecondCoefficient
    (H : AddSubgroup W.Point) [Fintype H] (P : H) (hP : P ≠ 0)
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) :
    residueMatrixRow H P = localSecondCoefficient H P * subgroupResidue H P := by
  classical
  have hd : P + P ≠ 0 := fun h => hno2 P hP (eq_neg_iff_add_eq_zero.mpr h)
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hdd : (P : W.Point) + (P : W.Point) ≠ 0 := fun h => hd (Subtype.ext h)
  have hy := short_y_ne_zero hp hdd
  let a := affineX (P : W.Point)
  let y := affineY (P : W.Point)
  let s := subgroupXRoots H
  let D := (BarycentricResidue.cofactor s id a).eval a
  have hi : a ∈ s := subgroupXRoots_mem H P hP
  have hinj : Set.InjOn (id : K → K) s := fun _ _ _ _ h => h
  have hD : D ≠ 0 := BarycentricResidue.cofactor_value_ne_zero hinj hi
  have hr := BarycentricResidue.finite_residue_identity hinj hi
  have hl : subgroupResidue H P = D⁻¹ / (2*y) := by
    unfold subgroupResidue subgroupNodalWeight
    rw [Lagrange.nodalWeight_eq_eval_nodal_erase_inv]
    rfl
  rw [residueMatrixRow_by_roots H P hP hno2 h₂]
  change affineX ((P : W.Point) + (P : W.Point)) * subgroupResidue H P - _ = _
  rw [short_doubling_x hp hdd]
  unfold localSecondCoefficient reciprocalTrace reciprocalSquareTrace
  rw [coefficientOthers_sum_by_roots H P hP hno2
      (fun v => 1 / (affineX (P : W.Point) - v)),
    coefficientOthers_sum_by_roots H P hP hno2
      (fun v => 1 / (affineX (P : W.Point) - v)^2), hl]
  change 2 * D *
      (∑ v ∈ s.erase a, subgroupNodalWeight H v / (a - v)^2) =
      -((∑ v ∈ s.erase a, 1 / (a - v))^2 +
        ∑ v ∈ s.erase a, (1 / (a - v))^2) at hr
  have he : (∑ v ∈ s.erase a, (1 / (a - v))^2) =
      ∑ v ∈ s.erase a, 1 / (a - v)^2 := by
    simp only [div_pow, one_pow]
  rw [he] at hr
  exact residue_coefficient_algebra _ _ _ _ _ _ _ h₂ hy hD hr

/-- An eigenvalue of the actual residue row is the actual second local coefficient. -/
theorem residue_eigenvector_localSecondCoefficient
    (H : AddSubgroup W.Point) [Fintype H] (P : H) (hP : P ≠ 0)
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) (u : K)
    (heigen : residueMatrixRow H P = u * subgroupResidue H P) :
    localSecondCoefficient H P = u := by
  have hd : P + P ≠ 0 := fun h => hno2 P hP (eq_neg_iff_add_eq_zero.mpr h)
  rw [residueMatrixRow_eq_localSecondCoefficient H P hP hno2 h₂] at heigen
  exact mul_right_cancel₀ (subgroupResidue_ne_zero H P hP hd h₂) heigen

/-- The eigenvector condition forces a square identity with the actual coordinate trace. -/
theorem residue_eigenvector_square
    (H : AddSubgroup W.Point) [Fintype H] (P : H) (hP : P ≠ 0)
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) (u : K)
    (heigen : residueMatrixRow H P = u * subgroupResidue H P) :
    (slopeCoefficient H P)^2 = (Fintype.card H : K) * affineX (P : W.Point) +
      2*u - subgroupXTrace H := by
  have hd : P + P ≠ 0 := fun h => hno2 P hP (eq_neg_iff_add_eq_zero.mpr h)
  have h := localSecondCoefficient_relation H P hP hd h₂
  rw [residue_eigenvector_localSecondCoefficient H P hP hno2 h₂ u heigen] at h
  linear_combination -h

/-- The same forced square identity for the original explicit reciprocal-root coefficient. -/
theorem residue_eigenvector_explicit_square
    (H : AddSubgroup W.Point) [Fintype H] (P : H) (hP : P ≠ 0)
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) (u : K)
    (heigen : residueMatrixRow H P = u * subgroupResidue H P) :
    (localCoefficient H P)^2 = (Fintype.card H : K) * affineX (P : W.Point) +
      2*u - subgroupXTrace H := by
  rw [localCoefficient_eq_slopeCoefficient H P hP hno2 h₂]
  exact residue_eigenvector_square H P hP hno2 h₂ u heigen

end TRR08Geometry

#print axioms TRR08Geometry.subgroupResidue_eq_inverse_product
#print axioms TRR08Geometry.subgroupResidue_ne_zero
#print axioms TRR08Geometry.paired_add_x_difference
#print axioms TRR08Geometry.residue_summand_pair
#print axioms TRR08Geometry.residueMatrixRow_by_roots

#print axioms TRR08Geometry.residueMatrixRow_eq_localSecondCoefficient
#print axioms TRR08Geometry.residue_eigenvector_localSecondCoefficient
#print axioms TRR08Geometry.residue_eigenvector_square
#print axioms TRR08Geometry.residue_eigenvector_explicit_square
