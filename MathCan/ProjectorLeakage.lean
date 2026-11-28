import Init

/-!
NRF-10: semiring arithmetic skeleton for the squared-energy cross term.
The matrix-valued projector Gram identity, Jensen inequality, and Frobenius
motion bound are established in a written proof and exact rational oracle.
This Init-only file formalizes the scalar cross-term expansion without sorry.
-/

namespace MathCan.ProjectorLeakage

/-- A squared sum contains both cross channels. -/
theorem squared_sum_four_terms (a b : Nat) :
    (a + b) * (a + b) = a * a + a * b + b * a + b * b := by
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

/-- Reordering exposes two squared components and their interference. -/
theorem squared_sum_interference (a b : Nat) :
    (a + b) * (a + b) = (a * a + b * b) + (a * b + b * a) := by
  rw [squared_sum_four_terms]
  ac_rfl

/-- With no new dark injection, the transported energy is just the old energy. -/
theorem no_extra_channel (a : Nat) :
    (a + 0) * (a + 0) = a * a := by
  simp

#print axioms squared_sum_four_terms
#print axioms squared_sum_interference
#print axioms no_extra_channel

end MathCan.ProjectorLeakage
