import MathCan.NOR32UnknownSupportCoverage

/-!
# NOR-33: exact overlap-matched two-block attack counting

A public source selects a risk union U and its complement V. A matched
attack support contains a positions from U and b positions from V.
The blind attacker changes exactly z of those a positions and r-z of
the b positions. A fixed audit observes t_U positions of the former
and t_V positions of the latter.

The TOTAL number of matched attack sets is C(a,z)C(b,r-z).
The EXACT number of attacks avoiding every inspected position is
C(a-t_U,z)C(b-t_V,r-z).

For a uniform draw over the product of those finite sets, the ratio
of these counts is the miss probability. When two audits observe the
same counts t_U,t_V within the SAME matched support, their expected
detection is the same. This isolates the within-support inspection
allocation, rather than treating a novel support label as causal.
-/

namespace MathCan.NOR33OverlapMatchedCoverage

abbrev choose := MathCan.NOR23CoordinateAudit.binomial
abbrev inspectedCount := MathCan.NOR32UnknownSupportCoverage.inspectedCount
def kSubsets (xs : List Bool) (k : Nat) : List (List Bool) :=
  MathCan.NOR23CoordinateAudit.kSubsets xs k

/-- Number of possible fixed-radius attacks with z coordinates from
    risk-support block A and r-z from complementary block B. -/
def matchedTotalCount (a b : List Bool) (z r : Nat) : Nat :=
  (kSubsets a z).length * (kSubsets b (r-z)).length

/-- Number of altered-coordinate subsets that avoid every inspection
    within each part of the predeclared matched attack support. -/
def matchedMissCount (a b : List Bool) (z r : Nat) : Nat :=
  (kSubsets (a.filter (fun flag => !flag)) z).length *
    (kSubsets (b.filter (fun flag => !flag)) (r-z)).length

/-- The exact two-block count numerator/denominator factorization.
    The attack mechanism chooses independent uniformly selected subsets
    from each support part, subject to the fixed overlap count. -/
theorem exact_two_block_hypergeometric_counts
    (a b : List Bool) (z r : Nat) :
    (matchedMissCount a b z r, matchedTotalCount a b z r) =
      (choose (a.length - inspectedCount a) z *
          choose (b.length - inspectedCount b) (r-z),
       choose a.length z * choose b.length (r-z)) := by
  have ha := MathCan.NOR32UnknownSupportCoverage.exact_unknown_support_attack_miss_and_total a z
  have hb := MathCan.NOR32UnknownSupportCoverage.exact_unknown_support_attack_miss_and_total b (r-z)
  have ma : (kSubsets (a.filter (fun flag => !flag)) z).length =
      choose (a.length - inspectedCount a) z := congrArg Prod.fst ha
  have mb : (kSubsets (b.filter (fun flag => !flag)) (r-z)).length =
      choose (b.length - inspectedCount b) (r-z) := congrArg Prod.fst hb
  have ta : (kSubsets a z).length = choose a.length z := congrArg Prod.snd ha
  have tb : (kSubsets b (r-z)).length = choose b.length (r-z) := congrArg Prod.snd hb
  simp only [matchedMissCount, matchedTotalCount, ma, mb, ta, tb]

/-- An ideal exact-overlap matched attack distribution cannot distinguish
    two audit policies that inspect the same number of positions inside
    each of the SAME two support blocks. Their numerator and denominator
    of the uniform conditional miss probability are identical. -/
theorem same_within_block_counts_same_detection
    (a1 b1 a2 b2 : List Bool) (z r : Nat)
    (sameInSize : a1.length = a2.length)
    (sameOutSize : b1.length = b2.length)
    (sameInChecked : inspectedCount a1 = inspectedCount a2)
    (sameOutChecked : inspectedCount b1 = inspectedCount b2) :
    (matchedMissCount a1 b1 z r, matchedTotalCount a1 b1 z r) =
      (matchedMissCount a2 b2 z r, matchedTotalCount a2 b2 z r) := by
  rw [exact_two_block_hypergeometric_counts,
      exact_two_block_hypergeometric_counts]
  rw [sameInSize, sameOutSize, sameInChecked, sameOutChecked]

/-- Every member of a finite roster of audit policies with the same
    conditional block-inspection statistics has the same matched
    hypergeometric count pair, independently of ranking mechanism. -/
theorem finite_matched_auditor_equivalence
    (roster : List (List Bool × List Bool))
    (referenceIn referenceOut : List Bool) (z r : Nat)
    (valid : ∀ pair ∈ roster,
       pair.1.length = referenceIn.length ∧
       pair.2.length = referenceOut.length ∧
       inspectedCount pair.1 = inspectedCount referenceIn ∧
       inspectedCount pair.2 = inspectedCount referenceOut) :
    roster.map (fun pair =>
       (matchedMissCount pair.1 pair.2 z r,
        matchedTotalCount pair.1 pair.2 z r)) =
    roster.map (fun _ =>
       (matchedMissCount referenceIn referenceOut z r,
        matchedTotalCount referenceIn referenceOut z r)) := by
  apply List.map_congr_left
  intro pair hi
  obtain ⟨h1,h2,h3,h4⟩ := valid pair hi
  exact same_within_block_counts_same_detection
    pair.1 pair.2 referenceIn referenceOut z r h1 h2 h3 h4

/-- Even perfect knowledge of a historical overlap category cannot
    prevent a realized-schedule-informed attacker from choosing a
    different target outside the inspected set. -/
theorem schedule_informed_overlap_attack_can_evade
    {Coordinate : Type}
    (inspected : List Coordinate)
    (trueFuture : Coordinate → Int)
    (unseen : ∃ i : Coordinate, i ∉ inspected) :
    ∃ alteredFuture : Coordinate → Int,
      alteredFuture ≠ trueFuture ∧
      MathCan.NOR24SequentialWitness.readTranscript inspected trueFuture =
        MathCan.NOR24SequentialWitness.readTranscript inspected alteredFuture :=
  MathCan.NOR25UniformReserve.schedule_visible_attacker_has_identical_transcript
    inspected trueFuture unseen

#print axioms exact_two_block_hypergeometric_counts
#print axioms same_within_block_counts_same_detection
#print axioms finite_matched_auditor_equivalence
#print axioms schedule_informed_overlap_attack_can_evade

end MathCan.NOR33OverlapMatchedCoverage
