import MathCan.RHGaloisRowInputs

/-!
# RHD-06: finite residue and theta-weight certificates

These Init-only Lean theorems verify the arithmetic of a local residue
model and a necessary weight inequality. They do not construct the
published number-field primes, FieldOK, PlanEx, GeoOne, or TLiftK.
-/

namespace MathCan.RHLocalPlaceGates

/-- Residue equations for i and sqrt(5) modulo the prime 29. -/
def ImagRoot29 (u : Fin 29) : Prop :=
  (u.val * u.val + 1) % 29 = 0

def RealRoot29 (v : Fin 29) : Prop :=
  (v.val * v.val) % 29 = 5

theorem imaginary_roots_exact :
    ∀ u : Fin 29, ImagRoot29 u ↔ (u.val = 12 ∨ u.val = 17) := by
  decide

theorem real_roots_exact :
    ∀ v : Fin 29, RealRoot29 v ↔ (v.val = 11 ∨ v.val = 18) := by
  decide

/-- Two residue branches agree on the imaginary coordinate and differ
on the real sqrt(5) coordinate. This is a finite model only. -/
theorem compatible_residue_pair :
    ∃ p q : Fin 29 × Fin 29,
      ImagRoot29 p.1 ∧ RealRoot29 p.2 ∧
      ImagRoot29 q.1 ∧ RealRoot29 q.2 ∧
      p.1 = q.1 ∧ p.2 ≠ q.2 := by
  refine ⟨(⟨12, by decide⟩, ⟨11, by decide⟩),
    (⟨12, by decide⟩, ⟨18, by decide⟩), ?_⟩
  decide

/-- The local weight dominance limits d when the weight is bounded above
and the twist exponent is bounded below. -/
theorem dimension_ceiling_from_weight_bounds
    (d : Nat) (weight twist upper lower : Int)
    (hdom : (d : Int) + twist ≤ 2 * weight)
    (hupper : weight ≤ upper)
    (hlower : lower ≤ twist) :
    (d : Int) ≤ 2 * upper - lower := by
  omega

/-- Fixed twist and weight cannot obey the later-data dominance inequality
in every target dimension. -/
theorem fixed_weight_twist_cannot_cover_all_dimensions
    (weight twist : Int) :
    ¬ (∀ d : Nat, (d : Int) + twist ≤ 2 * weight) := by
  intro h
  have hb := h ((2 * weight - twist).toNat + 1)
  omega

#print axioms imaginary_roots_exact
#print axioms real_roots_exact
#print axioms compatible_residue_pair
#print axioms dimension_ceiling_from_weight_bounds
#print axioms fixed_weight_twist_cannot_cover_all_dimensions

end MathCan.RHLocalPlaceGates
