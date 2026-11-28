import MathCan.NOR34EightAtomMatchedCoverage
import MathCan.NOR25UniformReserve

/-!
NOR-35: atom-budget-preserving curvature reranking, and finite independent
within-atom uniform-reserve miss count products.

Original NOR-25 source/trial auditors inspect t_j coordinates from
old-risk atom j. NOR35 reassigns inspected coordinates WITHIN each
public atom but leaves t_j EXACT. Under an attack uniformly redrawn in
each atom with a fixed quota q_j, the exact conditional miss and total
counts stay the same. The theorem is for ANY number of atoms and in
particular the eight tail/magnitude/lag membership atoms.

A new reranking policy takes a deterministic public prefix c_j within
each atom and selects a random reserve u_j from remaining positions.
Conditional on an attack already fixed before private reserve coins,
a hit in the prefix rules out all misses, otherwise the exact missed
reserve counts per atom are C(N_j-r_j,u_j) out of C(N_j,u_j).
The independent product identity follows by induction on atoms.
No entropy, witness authenticity, or empirical ranking gain is claimed.
-/

namespace MathCan.NOR35IntraAtomCurvature

abbrev choose := MathCan.NOR23CoordinateAudit.binomial

/-- One atom after source-public deterministic prefix inspection.
    The Boolean residual mask marks attacked positions among indices
    not inspected by the prefix. -/
structure AtomReserve where
  targetedHit : Bool
  residualAttackMask : List Bool
  randomReserve : Nat

def atomMisses (stage : AtomReserve) : Nat :=
  MathCan.NOR25UniformReserve.missedReserveCount
    stage.targetedHit stage.residualAttackMask stage.randomReserve

def atomTotal (stage : AtomReserve) : Nat :=
  MathCan.NOR25UniformReserve.allReserveCount
    stage.residualAttackMask stage.randomReserve

def atomBinomialMisses (stage : AtomReserve) : Nat :=
  if stage.targetedHit then 0
  else choose
    (stage.residualAttackMask.length -
      (stage.residualAttackMask.filter (fun altered => altered)).length)
    stage.randomReserve

def atomBinomialTotal (stage : AtomReserve) : Nat :=
  choose stage.residualAttackMask.length stage.randomReserve

/-- Per-atom numerator and denominator, exact including detected
    targeted-prefix attacks. -/
theorem exact_intraatom_reserve_count (stage : AtomReserve) :
    (atomMisses stage,atomTotal stage) =
      (atomBinomialMisses stage,atomBinomialTotal stage) := by
  exact MathCan.NOR25UniformReserve.exact_two_stage_blind_count
    stage.targetedHit stage.residualAttackMask stage.randomReserve

/-- Joint no-hit count for independent, atom-stratified reserve draws. -/
def totalReserveWorlds : List AtomReserve → Nat
  | [] => 1
  | stage :: rest => atomTotal stage * totalReserveWorlds rest

def missedReserveWorlds : List AtomReserve → Nat
  | [] => 1
  | stage :: rest => atomMisses stage * missedReserveWorlds rest

def exactBinomialTotal : List AtomReserve → Nat
  | [] => 1
  | stage :: rest => atomBinomialTotal stage * exactBinomialTotal rest

def exactBinomialMisses : List AtomReserve → Nat
  | [] => 1
  | stage :: rest => atomBinomialMisses stage * exactBinomialMisses rest

/-- The complete arbitrary multi-atom miss/total pair is exactly the
    product of the corresponding finite binomial counts, conditional
    on independent within-atom uniform reserves. -/
theorem independent_intraatom_reserve_product
    (stages : List AtomReserve) :
    (missedReserveWorlds stages,totalReserveWorlds stages) =
      (exactBinomialMisses stages,exactBinomialTotal stages) := by
  induction stages with
  | nil => rfl
  | cons h tail ih =>
      have hhead := exact_intraatom_reserve_count h
      have hmiss := congrArg Prod.fst hhead
      have htotal := congrArg Prod.snd hhead
      have ihmiss := congrArg Prod.fst ih
      have ihtotal := congrArg Prod.snd ih
      simp only [Prod.fst, Prod.snd] at hmiss htotal ihmiss ihtotal
      apply Prod.ext
      · simp only [missedReserveWorlds,exactBinomialMisses]
        rw [hmiss,ihmiss]
      · simp only [totalReserveWorlds,exactBinomialTotal]
        rw [htotal,ihtotal]

/-- Exact atom quota sufficiency: each reranked audit that preserves
    its source/trial eight-atom inspection counts has the SAME
    hypergeometric attack numerator and denominator under every
    within-full-atom-uniform attack quota vector. -/
theorem quota_preserving_intraatom_reranking_is_neutral
    (original reranked : List (List Bool)) (attackQuotas : List Nat)
    (sameSizes : original.map List.length = reranked.map List.length)
    (sameInspectedCounts :
      original.map MathCan.NOR34EightAtomMatchedCoverage.inspectedCount =
        reranked.map MathCan.NOR34EightAtomMatchedCoverage.inspectedCount) :
    (MathCan.NOR34EightAtomMatchedCoverage.missedPlacements original attackQuotas,
     MathCan.NOR34EightAtomMatchedCoverage.totalPlacements original attackQuotas) =
    (MathCan.NOR34EightAtomMatchedCoverage.missedPlacements reranked attackQuotas,
     MathCan.NOR34EightAtomMatchedCoverage.totalPlacements reranked attackQuotas) := by
  exact MathCan.NOR34EightAtomMatchedCoverage.matched_atom_statistics_give_equal_count_pair
    original reranked attackQuotas sameSizes sameInspectedCounts

/-- Preserving quota counts also preserves the observed total audit
    charge for every finite atom roster. This is a finite sum identity
    over the atom inspection counts. -/
theorem equal_quotas_preserve_total_witness_queries
    (original reranked : List Nat)
    (same : original = reranked) :
    original.sum = reranked.sum := by
  rw [same]

/-- An attack hit by the source-public selected prefix gives zero
    miss worlds across the independent tail draws, even if the other
    atom miss products are large. -/
theorem targeted_prefix_hit_forces_joint_detection
    (h : AtomReserve) (rest : List AtomReserve)
    (alreadyHit : h.targetedHit = true) :
    missedReserveWorlds (h :: rest) = 0 := by
  simp [missedReserveWorlds,atomMisses,
    MathCan.NOR25UniformReserve.missedReserveCount,alreadyHit]

/-- A completely revealed partial audit still admits an alternative
    exact target sharing its entire inspected transcript. -/
theorem complete_schedule_visible_still_evadable
    {Coordinate : Type}
    (checked : List Coordinate) (target : Coordinate → Int)
    (unseen : ∃ i, i ∉ checked) :
    ∃ alternate : Coordinate → Int,
      alternate ≠ target ∧
      MathCan.NOR24SequentialWitness.readTranscript checked target =
        MathCan.NOR24SequentialWitness.readTranscript checked alternate := by
  exact MathCan.NOR25UniformReserve.schedule_visible_attacker_has_identical_transcript
    checked target unseen

#print axioms exact_intraatom_reserve_count
#print axioms independent_intraatom_reserve_product
#print axioms quota_preserving_intraatom_reranking_is_neutral
#print axioms equal_quotas_preserve_total_witness_queries
#print axioms targeted_prefix_hit_forces_joint_detection
#print axioms complete_schedule_visible_still_evadable

end MathCan.NOR35IntraAtomCurvature
