import MathCan.NOR35IntraAtomCurvature

/-!
NOR-36: calibration-aware fixed attacks against public within-atom prefixes.

The CALIBRATION transcript can determine a four-position changed-output
attack. As long as that attack is frozen BEFORE a fresh independent exact
uniform reserve is drawn, NOR25/35's conditional binomial formula still
holds. A public deterministic targeted prefix can lose coverage against
a policy-aware attacker who deliberately changes another coordinate
inside the SAME atom. The same total atom audit quota does not imply
identical detection for a NONuniform/attack-aware attack distribution.

This module proves a concrete finite two-position counterexample, exact
conditional reserve numerator/denominator under arbitrary calibration
and a finite-game exact best-response inequality conditional on a
globally optimal attack choice. The applied greedy experiment does not
assume its eight restarts find that global optimum.
-/

namespace MathCan.NOR36PolicyAwareCurvature

/-- Exact finite source-output changed-coordinate detection. -/
def detects (checked changed : List Nat) : Bool :=
  checked.any (fun i => changed.contains i)

/-- Publicly targeted position 0 misses an attacker selecting position 1,
    whereas an equal-budget alternative inspects that attack. -/
theorem deterministic_public_prefix_can_be_avoided :
    detects [0] [1] = false ∧ detects [1] [1] = true := by
  decide

/-- BOTH one-position audits have the same total detection count against
    the roster of all one-position attacks in this two-coordinate atom.
    This is the finite equal-atom-budget no-free-lunch control. -/
theorem equal_atom_budget_uniform_attack_mean :
    (if detects [0] [0] then 1 else 0) +
      (if detects [0] [1] then 1 else 0) =
    (if detects [1] [0] then 1 else 0) +
      (if detects [1] [1] then 1 else 0) := by
  decide

/-- A calibrated attacker can deterministically choose a changed set
    using any prior public transcript. The exact missed reserve count
    holds for that fixed choice conditioned on the prior transcript,
    with a genuinely independent subsequent uniform reserve. -/
theorem calibrated_attack_inherits_conditional_reserve_count
    {Calibration : Type}
    (calibration : Calibration)
    (changedMask : Calibration → List Bool)
    (targetedHit : Calibration → Bool)
    (randomReserve : Nat) :
    (MathCan.NOR25UniformReserve.missedReserveCount
        (targetedHit calibration) (changedMask calibration) randomReserve,
     MathCan.NOR25UniformReserve.allReserveCount
        (changedMask calibration) randomReserve) =
    (if targetedHit calibration then 0 else
      MathCan.NOR25UniformReserve.binomial
        ((changedMask calibration).length -
          ((changedMask calibration).filter (fun changed => changed)).length)
        randomReserve,
     MathCan.NOR25UniformReserve.binomial
        (changedMask calibration).length randomReserve) := by
  exact MathCan.NOR25UniformReserve.exact_two_stage_blind_count
    (targetedHit calibration) (changedMask calibration) randomReserve

/-- Extends the conditional reserve theorem from one atom to ANY finite
    number of independent original atom reserves. A greedy attacker
    determines the atom masks after seeing public calibration but before
    the fresh independent reserve coin draws. -/
theorem calibrated_multiatom_attack_inherits_exact_product
    {Calibration : Type}
    (calibration : Calibration)
    (attackStages : Calibration → List MathCan.NOR35IntraAtomCurvature.AtomReserve) :
    (MathCan.NOR35IntraAtomCurvature.missedReserveWorlds
       (attackStages calibration),
     MathCan.NOR35IntraAtomCurvature.totalReserveWorlds
       (attackStages calibration)) =
    (MathCan.NOR35IntraAtomCurvature.exactBinomialMisses
       (attackStages calibration),
     MathCan.NOR35IntraAtomCurvature.exactBinomialTotal
       (attackStages calibration)) := by
  exact MathCan.NOR35IntraAtomCurvature.independent_intraatom_reserve_product
    (attackStages calibration)

/-- Over the SAME finite roster of attacks, an exact least-detection
    response has detection cost no larger than any other feasible
    response. This is a conditional global-optimum statement and must
    not be imputed to an approximate greedy search. -/
theorem exact_policy_aware_minimum_is_no_worse
    {Attack : Type}
    (score : Attack → Nat)
    (roster : List Attack) (chosen another : Attack)
    (optimal : ∀ a ∈ roster, score chosen ≤ score a)
    (feasible : another ∈ roster) :
    score chosen ≤ score another := by
  exact optimal another feasible

/-- Both publicly identical inspection quotas can preserve exact
    uniform-within-eight-atom detection while a deliberately
    coordinate-specific changed set distinguishes the policies. -/
theorem matched_atom_quota_does_not_imply_robust_dominance :
    detects [0] [1] = false ∧
    detects [1] [1] = true ∧
    (if detects [0] [0] then 1 else 0) +
      (if detects [0] [1] then 1 else 0) =
    (if detects [1] [0] then 1 else 0) +
      (if detects [1] [1] then 1 else 0) := by
  decide

/-- Exact checked-value transcript indistinguishability after the
    attacker learns the complete realized audit schedule remains. -/
theorem realized_schedule_visible_attack_evasion
    {Coordinate : Type} (checked : List Coordinate)
    (target : Coordinate → Int)
    (unseen : ∃ i, i ∉ checked) :
    ∃ modified : Coordinate → Int,
      modified ≠ target ∧
      MathCan.NOR24SequentialWitness.readTranscript checked target =
      MathCan.NOR24SequentialWitness.readTranscript checked modified := by
  exact MathCan.NOR25UniformReserve.schedule_visible_attacker_has_identical_transcript
    checked target unseen

#print axioms deterministic_public_prefix_can_be_avoided
#print axioms equal_atom_budget_uniform_attack_mean
#print axioms calibrated_attack_inherits_conditional_reserve_count
#print axioms calibrated_multiatom_attack_inherits_exact_product
#print axioms exact_policy_aware_minimum_is_no_worse
#print axioms matched_atom_quota_does_not_imply_robust_dominance
#print axioms realized_schedule_visible_attack_evasion

end MathCan.NOR36PolicyAwareCurvature
