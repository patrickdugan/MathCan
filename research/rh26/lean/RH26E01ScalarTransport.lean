import Mathlib

/-!
# RH-26E-01: scalar transport (independent algebraic toy)

Source-only registration: ../RH26E01_REGISTRATION.md
The motivating formal statement is WeilTensorModels.StepBeta / StepAlpha in
leanprover-community/riemann-hypothesis at
c900e67c2fcd1fdb041685820bbd2b867fbc5a4b, lines 597-617
of src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean.

This file proves only field-level facts about nonzero scalar transport.
The original automorphic and theta-integral hypotheses are NOT imported.
-/

namespace RH26E01

variable {α : Type*} [Field α]

/-- Normalize beta's pair of transport equations without dividing. -/
theorem beta_normalized (u d c l c₁ : α)
    (hinv : u * d = 1) (hstep : c * l = u * c₁) :
    c₁ = d * c * l := by
  calc
    c₁ = (u * d) * c₁ := by simp [hinv]
    _ = d * (u * c₁) := by ring
    _ = d * (c * l) := congrArg (fun x : α => d * x) hstep.symm
    _ = d * c * l := by ring

/-- A nonzero target comparison scalar forces the beta L-value to be nonzero. -/
theorem beta_nonzero (u d c l c₁ : α)
    (hinv : u * d = 1) (hstep : c * l = u * c₁) (htarget : c₁ ≠ 0) :
    l ≠ 0 := by
  intro hl
  apply htarget
  calc
    c₁ = d * c * l := beta_normalized u d c l c₁ hinv hstep
    _ = 0 := by simp [hl]

/-- A nonzero source comparison scalar forces the alpha L-value to be nonzero. -/
theorem alpha_nonzero (d c l c₁ : α)
    (hstep : c = d * l * c₁) (hsource : c ≠ 0) :
    l ≠ 0 := by
  intro hl
  apply hsource
  calc
    c = d * l * c₁ := hstep
    _ = 0 := by simp [hl]

/-- Without a nonzero beta target, beta's equations admit a zero L-value. -/
theorem beta_no_target_counterexample :
    ∃ (u d c l c₁ : ℂ), u * d = 1 ∧ c * l = u * c₁ ∧ c₁ = 0 ∧ l = 0 := by
  refine ⟨1, 1, 1, 0, 0, ?_, ?_, rfl, rfl⟩
  · norm_num
  · norm_num

/-- With no inverse equation, a nonzero target can coexist with L = 0. -/
theorem beta_no_inverse_counterexample :
    ∃ (u d c l c₁ : ℂ), c * l = u * c₁ ∧ c₁ ≠ 0 ∧ l = 0 ∧ u * d ≠ 1 := by
  refine ⟨0, 0, 1, 0, 1, ?_, ?_, rfl, ?_⟩
  · norm_num
  · norm_num
  · norm_num

/-- Without the nonzero alpha source, alpha's equation admits L = 0. -/
theorem alpha_no_source_counterexample :
    ∃ (d c l c₁ : ℂ), c = d * l * c₁ ∧ c = 0 ∧ l = 0 := by
  refine ⟨1, 0, 0, 1, ?_, rfl, rfl⟩
  norm_num

end RH26E01

#print axioms RH26E01.beta_normalized
#print axioms RH26E01.beta_nonzero
#print axioms RH26E01.alpha_nonzero
#print axioms RH26E01.beta_no_target_counterexample
#print axioms RH26E01.beta_no_inverse_counterexample
#print axioms RH26E01.alpha_no_source_counterexample
