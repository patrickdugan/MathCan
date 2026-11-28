import MathCan.NOR36PolicyAwareCurvature
import MathCan.NOR35IntraAtomCurvature

/-!
NOR-37: randomized public curvature targeting with a genuinely uniform
within-atom exploration branch.

For an attacker-chosen altered-coordinate set FIXED before private
inspection coins are drawn, the full-uniform atom-inspection branch
detects according to exact hypergeometric counting. Assigning positive
uniform probability mass to that branch gives an explicit nonzero
CONDITIONAL detection floor if the atom is inspected and attacked.
The other public curvature-targeting branch can have arbitrary
nonnegative detection, including zero against an informed attacker.

The finite counting identity for a uniform-within-atom altered quota
remains equal across same-atom-budget auditors regardless of within-
atom ranking. This result distinguishes conditional blind-attack
guarantees from the fully schedule-informed transcript collision.
-/

namespace MathCan.NOR37RandomizedCurvature

abbrev choose := MathCan.NOR23CoordinateAudit.binomial

/-- An exact integer numerator for a p/Q explore-versus-targeted
    stochastic mixture of TWO detection frequencies measured against
    the SAME fixed precommitted altered-position set. Q denotes
    a common schedule-count unit rather than genuine probability
    storage; all quantities are nonnegative. -/
def mixedDetectionNumerator
    (exploreWeight totalWeight uniformHits targetedHits : Nat) : Nat :=
  exploreWeight * uniformHits +
    (totalWeight - exploreWeight) * targetedHits

/-- Exact guarantee: a targeted branch cannot reduce the nonnegative
    contribution from the independently hidden full-uniform branch. -/
theorem positive_exploration_weight_guarantees_coverage
    (exploreWeight totalWeight uniformHits targetedHits : Nat) :
    exploreWeight * uniformHits ≤
      mixedDetectionNumerator exploreWeight totalWeight
        uniformHits targetedHits := by
  simp [mixedDetectionNumerator]

/-- Whenever a blind changed coordinate has positive probability of
    being inspected on the explore branch, positive explore mass
    gives a strictly positive total mixed detection numerator. -/
theorem strict_detection_when_exploration_can_hit
    (exploreWeight totalWeight uniformHits targetedHits : Nat)
    (hExplore : 0 < exploreWeight)
    (hUniformHit : 0 < uniformHits) :
    0 < mixedDetectionNumerator exploreWeight totalWeight
      uniformHits targetedHits := by
  have h : 0 < exploreWeight * uniformHits :=
    Nat.mul_pos hExplore hUniformHit
  have hfloor := positive_exploration_weight_guarantees_coverage
    exploreWeight totalWeight uniformHits targetedHits
  exact Nat.lt_of_lt_of_le h hfloor

/-- The equal-budget all-coordinates uniform draw remains an exactly
    enumerated conditional baseline, even when the attacked set was
    learned on an earlier public calibration transcript. -/
theorem calibration_chosen_blind_attack_has_exact_reserve_count
    {Calibration : Type}
    (record : Calibration)
    (fixedAltered : Calibration → List Bool)
    (uniformDraw : Nat) :
    (MathCan.NOR25UniformReserve.missedReserveCount
       false (fixedAltered record) uniformDraw,
     MathCan.NOR25UniformReserve.allReserveCount
       (fixedAltered record) uniformDraw) =
    (choose ((fixedAltered record).length -
       ((fixedAltered record).filter (fun b => b)).length) uniformDraw,
     choose (fixedAltered record).length uniformDraw) := by
  simpa [choose] using
    MathCan.NOR25UniformReserve.exact_two_stage_blind_count
      false (fixedAltered record) uniformDraw

/-- Conditional uniform-within-atom altered quota detection is
    unchanged when original and stochastic curvature audits each
    inspect the same NUMBER in every risk atom, even if they select
    entirely different inspected positions. -/
theorem stochastic_atom_quota_invariant_for_uniform_attack
    (original randomized : List (List Bool))
    (attackedQuota : List Nat)
    (samePopulation : original.map List.length =
                      randomized.map List.length)
    (sameInspected :
      original.map MathCan.NOR34EightAtomMatchedCoverage.inspectedCount =
      randomized.map MathCan.NOR34EightAtomMatchedCoverage.inspectedCount) :
    (MathCan.NOR34EightAtomMatchedCoverage.missedPlacements
       original attackedQuota,
     MathCan.NOR34EightAtomMatchedCoverage.totalPlacements
       original attackedQuota) =
    (MathCan.NOR34EightAtomMatchedCoverage.missedPlacements
       randomized attackedQuota,
     MathCan.NOR34EightAtomMatchedCoverage.totalPlacements
       randomized attackedQuota) := by
  exact MathCan.NOR34EightAtomMatchedCoverage.matched_atom_statistics_give_equal_count_pair
    original randomized attackedQuota samePopulation sameInspected

/-- Randomization must keep a positive exploration branch; with
    weight 0 the covered probability may vanish even if the full
    uniform branch could detect an attacker. -/
theorem zero_exploration_can_be_fully_avoided :
    mixedDetectionNumerator 0 4 1 0 = 0 := by
  decide

/-- A public inspection schedule revealed before the attacked
    coefficients are chosen still permits an altered target with
    exactly the same externally checked transcript. -/
theorem revealed_stochastic_schedule_still_evadable
    {Coordinate : Type}
    (checked : List Coordinate) (trueFuture : Coordinate → Int)
    (hasUnchecked : ∃ i, i ∉ checked) :
    ∃ modified : Coordinate → Int,
      modified ≠ trueFuture ∧
      MathCan.NOR24SequentialWitness.readTranscript checked trueFuture =
      MathCan.NOR24SequentialWitness.readTranscript checked modified := by
  exact MathCan.NOR25UniformReserve.schedule_visible_attacker_has_identical_transcript
    checked trueFuture hasUnchecked

#print axioms positive_exploration_weight_guarantees_coverage
#print axioms strict_detection_when_exploration_can_hit
#print axioms calibration_chosen_blind_attack_has_exact_reserve_count
#print axioms stochastic_atom_quota_invariant_for_uniform_attack
#print axioms zero_exploration_can_be_fully_avoided
#print axioms revealed_stochastic_schedule_still_evadable

end MathCan.NOR37RandomizedCurvature
