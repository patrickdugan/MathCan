import Init

/-!
# TRR-07: field algebra behind the interpolation obstruction

These theorems formalize the algebra after the geometric residue and cocycle
identities have been supplied. They apply to every `Lean.Grind.Field`, including
positive characteristic. They do not construct an elliptic curve, a function
field, a residue map, or the evaluation hyperplane. Those geometric statements
remain obligations of the written argument.
-/

namespace MathCan.TranslationInterpolationAlgebra

open Lean.Grind

variable {K : Type} [Field K]

/-- Subtract the two local constant-term identities. -/
theorem residue_difference (a b u v x y n c : K)
    (h₁ : 2*u-a^2 = c-n*x)
    (h₂ : 2*v-b^2 = c-n*y) :
    2*(u-v) = a^2-b^2-n*(x-y) := by
  grind

/-- In matching characteristic, the cocycle doubles the local coefficient. -/
theorem matching_characteristic_difference (a b u v x y n : K)
    (h : 2*(u-v) = a^2-b^2-n*(x-y))
    (hn : n = 0) (ha : a = 2*b) :
    2*(u-v) = 3*b^2 := by
  grind

/-- The final contradiction needs characteristic different from three and a
    nonzero logarithmic coefficient. No geometric premise is hidden here. -/
theorem matching_characteristic_exclusion (b u v : K)
    (h : 2*(u-v) = 3*b^2) (hb : b ≠ 0) (h₃ : (3 : K) ≠ 0) :
    u ≠ v := by
  intro huv
  have hz : 3*b^2 = 0 := by grind
  cases Field.of_mul_eq_zero hz with
  | inl hzero => exact h₃ hzero
  | inr hzero => exact hb (Field.of_pow_eq_zero b 2 hzero)

/-- A fixed pair of residues agrees exactly when the geometric obstruction
    agrees, once characteristic two is excluded. -/
theorem residue_constancy_iff (a b u v x y n : K)
    (h : 2*(u-v) = a^2-b^2-n*(x-y)) (h₂ : (2 : K) ≠ 0) :
    u = v ↔ a^2-n*x = b^2-n*y := by
  constructor
  · intro huv
    grind
  · intro he
    have hz : 2*(u-v) = 0 := by grind
    cases Field.of_mul_eq_zero hz with
    | inl hzero => exact False.elim (h₂ hzero)
    | inr hzero => grind

/-- Assigning a value at the identity changes the annihilator equation by
    the negation permutation, whose action on the odd residue is -lambda. -/
theorem pole_assignment_eigenvector (m u l : K) :
    m + u*(-l) = 0 ↔ m = u*l := by
  grind

/-- Multiplying a nonzero residue coordinate leaves its eigenvector equation
    equivalent. This is the componentwise step for a rescaled residue vector. -/
theorem eigenvector_scaling (m u l s : K) (hs : s ≠ 0) :
    s*m = u*(s*l) ↔ m = u*l := by
  constructor
  · intro h
    have hz : s*(m-u*l) = 0 := by grind
    cases Field.of_mul_eq_zero hz with
    | inl hzero => exact False.elim (hs hzero)
    | inr hzero => grind
  · intro h
    grind

/-- The diagonal correction cancels a row's residual. -/
theorem diagonal_correction (m l : K) (hl : l ≠ 0) :
    m + (-m/l)*l = 0 := by
  have hi : l⁻¹*l = 1 := Field.inv_mul_cancel hl
  rw [Field.div_eq_mul_inv]
  grind

/-- A symmetric array with row annihilator lambda has the same column
    annihilator. The finite sum is supplied as a function on rows, so this
    statement needs no choice of enumeration. -/
theorem symmetric_row_column {I : Type}
    (M : I → I → K) (annihilate : (I → K) → K)
    (hsym : ∀ i j, M i j = M j i)
    (hrow : ∀ i, annihilate (M i) = 0) :
    ∀ j, annihilate (fun i => M i j) = 0 := by
  intro j
  have he : (fun i => M i j) = M j := by
    funext i
    exact hsym i j
  rw [he]
  exact hrow j

/-- Additivity of the logarithmic cocycle gives its doubled value. -/
theorem cocycle_double {G : Type} (add : G → G → G) (a : G → K)
    (hadd : ∀ q r, a (add q r) = a q + a r) (q : G) :
    a (add q q) = 2*a q := by
  have h := hadd q q
  grind

#print axioms residue_difference
#print axioms matching_characteristic_difference
#print axioms matching_characteristic_exclusion
#print axioms residue_constancy_iff
#print axioms pole_assignment_eigenvector
#print axioms eigenvector_scaling
#print axioms diagonal_correction
#print axioms symmetric_row_column
#print axioms cocycle_double

end MathCan.TranslationInterpolationAlgebra
