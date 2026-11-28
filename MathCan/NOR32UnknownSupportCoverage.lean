import MathCan.NOR31ClassCollapsedMinimax

/-!
# NOR-32: unknown-support exact audit coverage and a uniform-attack duality

NOR-23 counted how often a uniform audit of k sampled coordinates detects
a fixed r-coordinate altered target. NOR-32 exchanges the randomization:
the AUDIT is fixed and a blind attacker samples a uniform r-subset from
an arbitrary declared support of size s. The exact miss count is then
C(s-t,r), where t is how many support positions the audit inspects.

When the attack support is the ENTIRE m-coordinate future, every fixed
k-coordinate audit plan has exactly C(m-k,r) undetected altered r-subsets
among C(m,r) equally weighted alternatives. Thus every mixture over
k-coordinate schedules has the SAME average success under this uniform
attack distribution, regardless of its source-risk ranking. A policy
that improves on selected nonuniform supports cannot strictly dominate
uniform auditing on ALL attack sets of radius r.

The finite arithmetic is kernel-checked. The probabilistic reading
assumes uniform independently drawn altered r-subsets and authentic
exact target-output witness values. It makes no statement about how
well the prior source-support templates generalize.
-/

namespace MathCan.NOR32UnknownSupportCoverage

abbrev choose := MathCan.NOR23CoordinateAudit.binomial

/-- Boolean mask of which coordinates in a DECLARED adversarial
    support were actually inspected by a fixed auditor. -/
def inspectedCount (mask : List Bool) : Nat :=
  (mask.filter (fun b => b)).length

/-- Every distinct r-subset of the support is a possible altered target. -/
def candidateAttacks (supportMask : List Bool) (radius : Nat) : Nat :=
  (MathCan.NOR23CoordinateAudit.kSubsets supportMask radius).length

/-- Blind attack placements compatible with a completely clean audit
    can choose only positions in the support that the audit did not see. -/
def undetectedAttackPlacements (supportMask : List Bool) (radius : Nat) : Nat :=
  (MathCan.NOR23CoordinateAudit.kSubsets
    (supportMask.filter (fun b => !b)) radius).length

/-- The exact count dual to NOR-23:
    with s support indices and t audited support indices,
    there are C(s-t,r) missed attacks and C(s,r) total attacks. -/
theorem exact_unknown_support_attack_miss_and_total
    (supportMask : List Bool) (radius : Nat) :
    (undetectedAttackPlacements supportMask radius,
     candidateAttacks supportMask radius) =
    (choose (supportMask.length - inspectedCount supportMask) radius,
     choose supportMask.length radius) := by
  exact MathCan.NOR23CoordinateAudit.exact_hypergeometric_miss_pair
    supportMask radius

/-- The exact integer numerator/denominator pair is the data required
    to interpret a conditional uniform-r attack miss probability.
    Its probability interpretation is C(s-t,r)/C(s,r) whenever the
    denominator is positive. Coercion to a rational implementation is
    deliberately kept outside this standalone Init-only module. -/
theorem exact_unknown_support_probability_numerator_denominator
    (supportMask : List Bool) (radius : Nat) :
    (undetectedAttackPlacements supportMask radius,
     candidateAttacks supportMask radius) =
    (choose (supportMask.length - inspectedCount supportMask) radius,
     choose supportMask.length radius) :=
  exact_unknown_support_attack_miss_and_total supportMask radius

/-- Under a uniform r-attack distribution on the full m-coordinate
    future, two fixed audits of the same k positions have IDENTICAL
    undetected and total attack counts. All coordinate rankings are
    covered. The ideal uniform attacker average is policy-invariant. -/
theorem equal_budget_uniform_attack_detectability
    (auditA auditB : List Bool) (radius : Nat)
    (sameUniverse : auditA.length = auditB.length)
    (sameBudget : inspectedCount auditA = inspectedCount auditB) :
    (undetectedAttackPlacements auditA radius,
     candidateAttacks auditA radius) =
    (undetectedAttackPlacements auditB radius,
     candidateAttacks auditB radius) := by
  calc
    (undetectedAttackPlacements auditA radius,
     candidateAttacks auditA radius) =
      (choose (auditA.length - inspectedCount auditA) radius,
       choose auditA.length radius) :=
        exact_unknown_support_attack_miss_and_total auditA radius
    _ = (choose (auditB.length - inspectedCount auditB) radius,
         choose auditB.length radius) := by
          rw [sameUniverse, sameBudget]
    _ = (undetectedAttackPlacements auditB radius,
         candidateAttacks auditB radius) :=
          (exact_unknown_support_attack_miss_and_total auditB radius).symm

/-- Every component of an arbitrarily randomized finite equal-budget
    audit mixture has the same mean under uniform blind attacks. Hence
    randomizing or concentrating the inspected positions cannot change
    this particular attack-distribution average. -/
theorem finite_audit_mixture_uniform_attack_counts_invariant
    (audits : List (List Bool)) (reference : List Bool) (radius : Nat)
    (valid : ∀ inspected ∈ audits,
      inspected.length = reference.length ∧
      inspectedCount inspected = inspectedCount reference) :
    audits.map (fun inspected =>
      (undetectedAttackPlacements inspected radius,
       candidateAttacks inspected radius)) =
    audits.map (fun _ =>
      (undetectedAttackPlacements reference radius,
       candidateAttacks reference radius)) := by
  apply List.map_congr_left
  intro inspected hi
  obtain ⟨hlen, hbudget⟩ := valid inspected hi
  exact equal_budget_uniform_attack_detectability
    inspected reference radius hlen hbudget

/-- The complete-schedule-informed attacker is still able to change
    an uninspected integer coefficient and obtain the identical
    ordered exact-value transcript, provided an unchecked position exists. -/
theorem informed_unknown_support_counterexample
    {Coordinate : Type}
    (inspected : List Coordinate)
    (trueTarget : Coordinate → Int)
    (hasUnchecked : ∃ i : Coordinate, i ∉ inspected) :
    ∃ changedTarget : Coordinate → Int,
      changedTarget ≠ trueTarget ∧
      MathCan.NOR24SequentialWitness.readTranscript inspected trueTarget =
        MathCan.NOR24SequentialWitness.readTranscript inspected changedTarget := by
  exact MathCan.NOR25UniformReserve.schedule_visible_attacker_has_identical_transcript
    inspected trueTarget hasUnchecked

#print axioms exact_unknown_support_attack_miss_and_total
#print axioms exact_unknown_support_probability_numerator_denominator
#print axioms equal_budget_uniform_attack_detectability
#print axioms finite_audit_mixture_uniform_attack_counts_invariant
#print axioms informed_unknown_support_counterexample

end MathCan.NOR32UnknownSupportCoverage
