import Init

/-!
# TRR-07: algebraic classification of the degree-eight obstruction

The geometric argument supplies the first four coefficients of a polynomial
identity. This module proves that those coefficients force a singular short
Weierstrass cubic. The root count, slope cocycle, and passage from a decoder to
these coefficient hypotheses remain explicit geometric proof obligations.
-/

namespace MathCan.TranslationInterpolationUniform

open Lean.Grind

variable {K : Type} [Field K]

theorem product_nonzero {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 := by
  intro h
  cases Field.of_mul_eq_zero h with
  | inl hz => exact ha hz
  | inr hz => exact hb hz

theorem power_nonzero {a : K} (ha : a ≠ 0) (m : Nat) : a^m ≠ 0 := by
  intro hz
  exact ha (Field.of_pow_eq_zero a m hz)

theorem cancel_nonzero {a z : K} (ha : a ≠ 0) (h : a*z = 0) : z = 0 := by
  cases Field.of_mul_eq_zero h with
  | inl hz => exact False.elim (ha hz)
  | inr hz => exact hz

theorem normalized_singular (A B c : K)
    (hA : 4*A = -3*c^2) (hB : 4*B = c^3)
    (h₂ : (2 : K) ≠ 0) :
    4*A^3+27*B^2 = 0 := by
  have h : 64*(4*A^3+27*B^2) = 0 := by grind
  cases Field.of_mul_eq_zero h with
  | inr hz => exact hz
  | inl hz =>
      have hp : (2 : K)^6 = 0 := by grind
      exact False.elim (h₂ (Field.of_pow_eq_zero (2 : K) 6 hp))

/-- The branch 9*n=25 has characteristic different from five when n is nonzero. -/
theorem second_branch_five_nonzero (n : K) (hn : n ≠ 0)
    (h₃ : (3 : K) ≠ 0) (h : 9*n = 25) : (5 : K) ≠ 0 := by
  intro h₅
  have hz : 9*n = 0 := by grind
  cases Field.of_mul_eq_zero hz with
  | inr hz => exact hn hz
  | inl hz =>
      have hp : (3 : K)^2 = 0 := by grind
      exact h₃ (Field.of_pow_eq_zero (3 : K) 2 hp)

/-- Classification from the leading four coefficients of the degree-eight
    obstruction. The hypotheses are polynomial equalities over the field. -/
theorem leading_coefficients_force_singularity (n A B c : K)
    (hn : n ≠ 0) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (h8 : 9*(n-1)*(9*n-25) = 0)
    (h7 : -360*c*(n-1) = 0)
    (h6 : 108*A*n^2-456*A*n+540*A+144*c^2 = 0)
    (h5 : -600*A*c*n+792*A*c-144*B*n+720*B = 0) :
    4*A^3+27*B^2 = 0 := by
  have h9 : (9 : K) ≠ 0 := by
    intro hz
    have hp : (3 : K)^2 = 0 := by grind
    exact h₃ (Field.of_pow_eq_zero (3 : K) 2 hp)
  have hb : n-1 = 0 ∨ 9*n-25 = 0 := by
    cases Field.of_mul_eq_zero h8 with
    | inr hz => exact Or.inr hz
    | inl hz =>
        cases Field.of_mul_eq_zero hz with
        | inl hz => exact False.elim (h9 hz)
        | inr hz => exact Or.inl hz
  cases hb with
  | inl hcase =>
      have heq : n = 1 := by grind
      have hA0 : (2 : K)^4*3*(4*A+3*c^2) = 0 := by grind
      have hA1 := cancel_nonzero (product_nonzero (power_nonzero h₂ 4) h₃) hA0
      have hA : 4*A = -3*c^2 := by grind
      have hB0 : (2 : K)^4*3^2*(4*B-c^3) = 0 := by grind
      have hB1 := cancel_nonzero
        (product_nonzero (power_nonzero h₂ 4) (power_nonzero h₃ 2)) hB0
      have hB : 4*B = c^3 := by grind
      exact normalized_singular A B c hA hB h₂
  | inr hcase =>
      have heq : 9*n = 25 := by grind
      have h₅ := second_branch_five_nonzero n hn h₃ heq
      have hc0 : (2 : K)^7*3^2*5*c = 0 := by grind
      have hc := cancel_nonzero
        (product_nonzero (product_nonzero (power_nonzero h₂ 7) (power_nonzero h₃ 2)) h₅) hc0
      have hA0 : (2 : K)^6*3^3*5*A = 0 := by grind
      have hA := cancel_nonzero
        (product_nonzero (product_nonzero (power_nonzero h₂ 6) (power_nonzero h₃ 3)) h₅) hA0
      have hB0 : (2 : K)^6*3^2*5*B = 0 := by grind
      have hB := cancel_nonzero
        (product_nonzero (product_nonzero (power_nonzero h₂ 6) (power_nonzero h₃ 2)) h₅) hB0
      grind

#print axioms product_nonzero
#print axioms power_nonzero
#print axioms cancel_nonzero
#print axioms normalized_singular
#print axioms second_branch_five_nonzero
#print axioms leading_coefficients_force_singularity

end MathCan.TranslationInterpolationUniform
