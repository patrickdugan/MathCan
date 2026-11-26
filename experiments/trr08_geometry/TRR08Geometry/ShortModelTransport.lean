module

public import TRR08Geometry.GeneralCoordinates

/-!
# Additive transport to a short Weierstrass model
-/

@[expose] public section
namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type} [Field K]

/-- Send points on the sheared model back to the original curve. -/
noncomputable def shearPointTo (W : Affine K) [W.IsElliptic] (r s t : K) :
    (shearModel W r s t).Point → W.Point
  | .zero => .zero
  | .some x y h => Affine.Point.mk ((shear_equation_iff W r s t x y).mp h.1)

/-- The inverse shear on actual curve points. -/
noncomputable def shearPointFrom (W : Affine K) [W.IsElliptic] (r s t : K) :
    W.Point → (shearModel W r s t).Point
  | .zero => .zero
  | .some x y h => Affine.Point.mk ((shear_equation_iff W r s t
      (x-r) (y-s*(x-r)-t)).mpr (by convert h.1 using 1 <;> ring))

theorem shearPointTo_from (W : Affine K) [W.IsElliptic] (r s t : K)
    (P : W.Point) : shearPointTo W r s t (shearPointFrom W r s t P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [shearPointFrom, shearPointTo, Affine.Point.mk, Affine.Point.some.injEq]
    constructor <;> ring

theorem shearPointFrom_to (W : Affine K) [W.IsElliptic] (r s t : K)
    (P : (shearModel W r s t).Point) :
    shearPointFrom W r s t (shearPointTo W r s t P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [shearPointFrom, shearPointTo, Affine.Point.mk, Affine.Point.some.injEq]
    constructor <;> ring

variable [DecidableEq K]

theorem shearPointTo_add (W : Affine K) [W.IsElliptic] (r s t : K)
    (P Q : (shearModel W r s t).Point) :
    shearPointTo W r s t (P+Q) = shearPointTo W r s t P + shearPointTo W r s t Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁=x₂ ∧ y₁=(shearModel W r s t).negY x₂ y₂
      · have hold := (shear_inverse_pair_iff W r s t x₁ x₂ y₁ y₂).mpr hxy
        rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        simp only [shearPointTo, Affine.Point.mk]
        exact (Affine.Point.add_of_Y_eq hold.1 hold.2).symm
      · have hold : ¬(x₁+r=x₂+r ∧ y₁+s*x₁+t=W.negY (x₂+r) (y₂+s*x₂+t)) := by
          rwa [shear_inverse_pair_iff]
        rw [Affine.Point.add_some hxy]
        simp only [shearPointTo, Affine.Point.mk]
        rw [Affine.Point.add_some hold, Affine.Point.some.injEq]
        rw [shear_slope W r s t h₁.1 h₂.1 hxy]
        exact ⟨(shear_addX W r s t x₁ x₂ _).symm,
          (shear_addY W r s t x₁ x₂ y₁ _).symm⟩

/-- Actual additive equivalence induced by the coordinate shear. -/
noncomputable def shearPointEquiv (W : Affine K) [W.IsElliptic] (r s t : K) :
    (shearModel W r s t).Point ≃+ W.Point where
  toFun := shearPointTo W r s t
  invFun := shearPointFrom W r s t
  left_inv := shearPointFrom_to W r s t
  right_inv := shearPointTo_from W r s t
  map_add' := shearPointTo_add W r s t

theorem shearPointEquiv_x (W : Affine K) [W.IsElliptic] (r s t : K)
    {P : (shearModel W r s t).Point} (hP : P ≠ 0) :
    affineX (shearPointEquiv W r s t P) = affineX P+r := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h => rfl

theorem shearPointEquiv_y (W : Affine K) [W.IsElliptic] (r s t : K)
    {P : (shearModel W r s t).Point} (hP : P ≠ 0) :
    affineY (shearPointEquiv W r s t P) = affineY P+s*affineX P+t := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h => rfl

omit [DecidableEq K] in
theorem toShortNF_unit (W : Affine K) [Invertible (2 : K)] [Invertible (3 : K)] :
    W.toShortNF.u = 1 := by
  simp [WeierstrassCurve.toShortNF, WeierstrassCurve.toCharNeTwoNF,
    VariableChange.mul_def]

omit [DecidableEq K] in
theorem shearModel_toShortNF (W : Affine K) [Invertible (2 : K)] [Invertible (3 : K)] :
    shearModel W W.toShortNF.r W.toShortNF.s W.toShortNF.t = W.toShortNF • W := by
  unfold shearModel
  have hC : VariableChange.mk 1 W.toShortNF.r W.toShortNF.s W.toShortNF.t = W.toShortNF := by
    ext
    · simp only [toShortNF_unit, Units.val_one]
    · rfl
    · rfl
    · rfl
  rw [hC]

instance shortShear_isShortNF (W : Affine K) [Invertible (2 : K)] [Invertible (3 : K)] :
    (shearModel W W.toShortNF.r W.toShortNF.s W.toShortNF.t).IsShortNF := by
  rw [shearModel_toShortNF]
  infer_instance

/-- The additive equivalence from the explicit short model back to the original. -/
noncomputable def shortPointEquiv (W : Affine K) [W.IsElliptic]
    [Invertible (2 : K)] [Invertible (3 : K)] :
    (shearModel W W.toShortNF.r W.toShortNF.s W.toShortNF.t).Point ≃+ W.Point :=
  shearPointEquiv W W.toShortNF.r W.toShortNF.s W.toShortNF.t

theorem shortPointEquiv_x (W : Affine K) [W.IsElliptic]
    [Invertible (2 : K)] [Invertible (3 : K)]
    {P : (shearModel W W.toShortNF.r W.toShortNF.s W.toShortNF.t).Point} (hP : P ≠ 0) :
    affineX (shortPointEquiv W P) = affineX P+W.toShortNF.r :=
  shearPointEquiv_x W _ _ _ hP

theorem shortPointEquiv_y (W : Affine K) [W.IsElliptic]
    [Invertible (2 : K)] [Invertible (3 : K)]
    {P : (shearModel W W.toShortNF.r W.toShortNF.s W.toShortNF.t).Point} (hP : P ≠ 0) :
    affineY (shortPointEquiv W P) =
      affineY P+W.toShortNF.s*affineX P+W.toShortNF.t :=
  shearPointEquiv_y W _ _ _ hP

end TRR08Geometry

#print axioms TRR08Geometry.shearPointTo_from
#print axioms TRR08Geometry.shearPointFrom_to
#print axioms TRR08Geometry.shearPointTo_add
#print axioms TRR08Geometry.shearPointEquiv_x
#print axioms TRR08Geometry.shearPointEquiv_y

#print axioms TRR08Geometry.toShortNF_unit
#print axioms TRR08Geometry.shearModel_toShortNF
#print axioms TRR08Geometry.shortPointEquiv_x
#print axioms TRR08Geometry.shortPointEquiv_y
