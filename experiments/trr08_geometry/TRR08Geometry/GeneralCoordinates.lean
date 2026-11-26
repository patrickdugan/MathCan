module

public import TRR08Geometry.MarkedPoints
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Coordinate shear between actual Weierstrass point groups

The change with unit scale one sends the coordinates of the changed model
back to the original model by `(x,y) ↦ (x+r,y+s*x+t)`.
-/

@[expose] public section
namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type} [Field K]

/-- The actual model induced by an admissible coordinate shear. -/
def shearModel (W : Affine K) (r s t : K) : Affine K :=
  (VariableChange.mk 1 r s t) • W

instance shearModel_isElliptic (W : Affine K) [W.IsElliptic] (r s t : K) :
    (shearModel W r s t).IsElliptic := by
  unfold shearModel
  infer_instance

theorem shear_equation_iff (W : Affine K) (r s t x y : K) :
    (shearModel W r s t).Equation x y ↔ W.Equation (x+r) (y+s*x+t) := by
  rw [Affine.equation_iff', Affine.equation_iff']
  simp only [shearModel, variableChange_def, inv_one, Units.val_one,
    one_pow, one_mul]
  ring_nf

theorem shear_negY (W : Affine K) (r s t x y : K) :
    W.negY (x+r) (y+s*x+t) = (shearModel W r s t).negY x y + s*x+t := by
  simp only [Affine.negY, shearModel, variableChange_def, inv_one, Units.val_one,
    one_pow, one_mul]
  ring

theorem shear_inverse_pair_iff (W : Affine K) (r s t x₁ x₂ y₁ y₂ : K) :
    (x₁+r=x₂+r ∧ y₁+s*x₁+t=W.negY (x₂+r) (y₂+s*x₂+t)) ↔
      (x₁=x₂ ∧ y₁=(shearModel W r s t).negY x₂ y₂) := by
  rw [shear_negY]
  constructor
  · rintro ⟨hx,hy⟩
    have hx' : x₁=x₂ := add_right_cancel hx
    refine ⟨hx', ?_⟩
    rw [hx'] at hy
    exact add_right_cancel (add_right_cancel hy)
  · rintro ⟨rfl,hy⟩
    exact ⟨rfl, by rw [hy]⟩

theorem shear_addX (W : Affine K) (r s t x₁ x₂ m : K) :
    W.addX (x₁+r) (x₂+r) (m+s) = (shearModel W r s t).addX x₁ x₂ m+r := by
  simp only [Affine.addX, shearModel, variableChange_def, inv_one, Units.val_one,
    one_pow, one_mul]
  ring

theorem shear_addY (W : Affine K) (r s t x₁ x₂ y₁ m : K) :
    W.addY (x₁+r) (x₂+r) (y₁+s*x₁+t) (m+s) =
      (shearModel W r s t).addY x₁ x₂ y₁ m +
        s*(shearModel W r s t).addX x₁ x₂ m+t := by
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, shearModel,
    variableChange_def, inv_one, Units.val_one, one_pow, one_mul]
  ring

variable [DecidableEq K]

theorem shear_slope (W : Affine K) (r s t : K) {x₁ x₂ y₁ y₂ : K}
    (h₁ : (shearModel W r s t).Equation x₁ y₁)
    (h₂ : (shearModel W r s t).Equation x₂ y₂)
    (hxy : ¬(x₁=x₂ ∧ y₁=(shearModel W r s t).negY x₂ y₂)) :
    W.slope (x₁+r) (x₂+r) (y₁+s*x₁+t) (y₂+s*x₂+t) =
      (shearModel W r s t).slope x₁ x₂ y₁ y₂ + s := by
  have hold : ¬(x₁+r=x₂+r ∧ y₁+s*x₁+t=W.negY (x₂+r) (y₂+s*x₂+t)) := by
    rwa [shear_inverse_pair_iff]
  by_cases hx : x₁=x₂
  · have hy : y₁ ≠ (shearModel W r s t).negY x₂ y₂ := fun h => hxy ⟨hx,h⟩
    have hyy := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    subst x₂
    subst y₂
    have hyo : y₁+s*x₁+t ≠ W.negY (x₁+r) (y₁+s*x₁+t) := fun h => hold ⟨rfl,h⟩
    rw [Affine.slope_of_Y_ne rfl hyo, Affine.slope_of_Y_ne rfl hy]
    have hden : (y₁+s*x₁+t)-W.negY (x₁+r) (y₁+s*x₁+t) =
        y₁-(shearModel W r s t).negY x₁ y₁ := by
      rw [shear_negY]
      ring
    rw [hden]
    have hd := sub_ne_zero.mpr hy
    field_simp
    simp only [shearModel, variableChange_def, inv_one, Units.val_one,
      one_pow, one_mul, Affine.negY]
    ring
  · have hxo : x₁+r ≠ x₂+r := fun h => hx (add_right_cancel h)
    rw [Affine.slope_of_X_ne hxo, Affine.slope_of_X_ne hx]
    have hd : x₁-x₂ ≠ 0 := sub_ne_zero.mpr hx
    have heq : (x₁+r)-(x₂+r)=x₁-x₂ := by ring
    rw [heq]
    field_simp
    ring

end TRR08Geometry

#print axioms TRR08Geometry.shear_equation_iff
#print axioms TRR08Geometry.shear_negY
#print axioms TRR08Geometry.shear_inverse_pair_iff
#print axioms TRR08Geometry.shear_addX
#print axioms TRR08Geometry.shear_addY

#print axioms TRR08Geometry.shear_slope
