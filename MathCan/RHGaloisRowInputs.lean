import MathCan.RHMainLogic

/-!
# RHD-04: Galois row from geometry and theta lifting.

An Init-only logical model of the verified source theorem boundaries.
This module does not recreate GeoOne, TLiftK, Row0b, the genuine
local Langlands representation, or any arithmetic-geometric proof.
-/

namespace MathCan.RHGaloisRowInputs

universe u

/-- Original source: galoisRepresentations_of_thetaLift composes
the GeoOne result with the TLiftK result and produces Row0b recT. -/
theorem galois_row_from_geometry_and_theta_lift
    {GeoOne TLiftK CoreAll Row0 Row0b : Prop}
    (geo : GeoOne) (lift : TLiftK)
    (produceCore : GeoOne → TLiftK → CoreAll)
    (produceRow : CoreAll → Row0)
    (strengthenRow : Row0 → Row0b) : Row0b :=
  strengthenRow (produceRow (produceCore geo lift))

/-- Source MainConclusion uses the same Row0b witness twice,
and the separately proved RecTExists as its third input. -/
theorem literature_inputs_from_row_and_recT
    {Row0b RecTExists : Prop} (row : Row0b) (rec : RecTExists) :
    MathCan.RHMainLogic.OpenLiteratureProxy Row0b RecTExists :=
  ⟨row, rec, row⟩

/-- A fixed initial unitary problem may choose a lifting threshold
before the target dimension and all subsequent local data are chosen. -/
def UniformEventualLift {Local : Type u}
    (Admissible : (d : Nat) → Local → Prop) : Prop :=
  ∃ d0 : Nat, ∀ d : Nat, d0 ≤ d → ∀ local : Local, Admissible d local

/-- The stronger source order of quantifiers implies eventual validity
for each particular later local datum. -/
theorem uniform_eventual_lift_implies_pointwise
    {Local : Type u}
    (Admissible : (d : Nat) → Local → Prop)
    (h : UniformEventualLift Admissible) :
    ∀ local : Local, ∃ d0 : Nat,
      ∀ d : Nat, d0 ≤ d → Admissible d local := by
  obtain ⟨d0, hd0⟩ := h
  intro local
  exact ⟨d0, fun d hd => hd0 d hd local⟩

/-- The inverse quantifier exchange is invalid in general. Each local
datum n may require d≥n, without one finite threshold for every n. -/
theorem pointwise_lift_thresholds_need_not_be_uniform :
    (∀ local : Nat, ∃ d0 : Nat,
        ∀ d : Nat, d0 ≤ d → local ≤ d) ∧
      ¬ (∃ d0 : Nat, ∀ d : Nat, d0 ≤ d →
        ∀ local : Nat, local ≤ d) := by
  constructor
  · intro local
    exact ⟨local, fun d hd => hd⟩
  · rintro ⟨d0, h⟩
    have hh := h d0 (Nat.le_refl d0) (d0 + 1)
    omega

/-- A separate parameter can change which initial problem is being
lifted, so the threshold need not be uniform across all initial problems. -/
theorem initial_data_can_change_lift_threshold :
    (∀ initial : Nat, ∃ d0 : Nat, ∀ d : Nat,
      d0 ≤ d → initial ≤ d) ∧
      ¬ (∃ d0 : Nat, ∀ initial d : Nat,
        d0 ≤ d → initial ≤ d) := by
  constructor
  · intro initial
    exact ⟨initial, fun d hd => hd⟩
  · rintro ⟨d0, h⟩
    have bad := h (d0 + 1) d0 (Nat.le_refl d0)
    omega

#print axioms galois_row_from_geometry_and_theta_lift
#print axioms literature_inputs_from_row_and_recT
#print axioms uniform_eventual_lift_implies_pointwise
#print axioms pointwise_lift_thresholds_need_not_be_uniform
#print axioms initial_data_can_change_lift_threshold

end MathCan.RHGaloisRowInputs
