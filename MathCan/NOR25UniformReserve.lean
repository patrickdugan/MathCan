import MathCan.NOR24SequentialWitness

/-!
# NOR-25: exact two-stage uniform-reserve audit and schedule-visible evasion

A finite verifier uses an arbitrary public-risk coordinate prefix followed
by an independently sampled uniform subset of the previously unchecked
coordinates. Condition on whether an attack touched the risk prefix.

For any fixed residual Boolean alteration mask, an undetected uniform
size-u reserve can select only unchanged positions. The exact number of
missed reserve schedules is C(N-r,u), where N is the length of that residual
mask and r is its number of true (altered) positions. The total number of
reserve schedules is C(N,u). An alteration in the targeted prefix already
makes the audit reject.

The formal statements concern finite enumeration, exact transcript values
and detectability. The interpretation as a probability uses idealized
uniform sampling independent of the attack, rather than public pseudorandom
seeds. A schedule-informed adversary can choose an unchecked difference.
-/

namespace MathCan.NOR25UniformReserve

universe u
variable {Coordinate : Type u}

abbrev binomial := MathCan.NOR23CoordinateAudit.binomial

/-- Whether the risk-targeted prefix has already encountered any
changed coefficient. The remaining mask indexes only unchecked positions. -/
def missedReserveCount
    (targetedHit : Bool) (remaining : List Bool) (reserve : Nat) : Nat :=
  if targetedHit then 0
  else (MathCan.NOR23CoordinateAudit.kSubsets (remaining.filter (fun modified => !modified)) reserve).length

/-- Each size-u position-subset of unchecked positions is an equally
likely audit schedule under ideal uniform sampling without replacement. -/
def allReserveCount (remaining : List Bool) (reserve : Nat) : Nat :=
  (MathCan.NOR23CoordinateAudit.kSubsets remaining reserve).length

/-- Exact numerator and denominator for any fixed attack after a
public-risk prefix. When the prefix hit, the miss numerator is zero.
Otherwise it is the hypergeometric C(N-r,u) count from the residual mask. -/
theorem exact_two_stage_blind_count
    (targetedHit : Bool) (remaining : List Bool) (reserve : Nat) :
    (missedReserveCount targetedHit remaining reserve,
     allReserveCount remaining reserve) =
    (if targetedHit then 0
       else binomial
         (remaining.length -
           (remaining.filter (fun modified => modified)).length)
         reserve,
     binomial remaining.length reserve) := by
  cases targetedHit with
  | false =>
      change
        ((MathCan.NOR23CoordinateAudit.kSubsets
            (remaining.filter (fun modified => !modified)) reserve).length,
         (MathCan.NOR23CoordinateAudit.kSubsets remaining reserve).length) =
        (binomial
           (remaining.length -
             (remaining.filter (fun modified => modified)).length) reserve,
         binomial remaining.length reserve)
      apply Prod.ext
      · exact MathCan.NOR23CoordinateAudit.fixed_attack_undetected_challenge_count
          remaining reserve
      · exact MathCan.NOR23CoordinateAudit.total_k_coordinate_challenges
          remaining reserve
  | true =>
      change
        (0, (MathCan.NOR23CoordinateAudit.kSubsets remaining reserve).length) =
        (0, binomial remaining.length reserve)
      apply Prod.ext
      · rfl
      · exact MathCan.NOR23CoordinateAudit.total_k_coordinate_challenges
          remaining reserve

/-- Choosing an audit prefix that already intersects the changed set
forces the two-stage verifier's no-hit count to vanish for every reserve. -/
theorem targeted_detection_is_certain
    (remaining : List Bool) (reserve : Nat) :
    missedReserveCount true remaining reserve = 0 := by
  rfl

/-- Adding an independent uniform reserve never increases the number
of missed schedules above the fixed-residual hypergeometric numerator. -/
theorem uniform_reserve_miss_count_bounded
    (targetedHit : Bool) (remaining : List Bool) (reserve : Nat) :
    missedReserveCount targetedHit remaining reserve ≤
      binomial
        (remaining.length -
          (remaining.filter (fun modified => modified)).length)
        reserve := by
  cases targetedHit with
  | false =>
      simp [missedReserveCount,
        MathCan.NOR23CoordinateAudit.fixed_attack_undetected_challenge_count]
  | true =>
      simp [missedReserveCount]

/-- Any exact mismatch found in the risk prefix remains a rejection
after appending any set of uniform exploration coordinates. -/
theorem extending_inspections_preserves_rejection
    (targeted randomReserve : List Coordinate)
    (candidate target : Coordinate → Int)
    (rejected : ¬ MathCan.NOR23CoordinateAudit.agreesOn targeted candidate target) :
    ¬ MathCan.NOR23CoordinateAudit.agreesOn
        (targeted ++ randomReserve) candidate target := by
  intro accepted
  apply rejected
  exact MathCan.NOR23CoordinateAudit.audit_agreement_monotone
    targeted (targeted ++ randomReserve) candidate target
    (by intro i hi; exact List.mem_append.mpr (Or.inl hi))
    accepted

/-- A visible changed coordinate in the targeted prefix is a
deterministic rejection independent of all subsequent random choices. -/
theorem inspected_targeted_change_is_detected
    (targeted randomReserve : List Coordinate)
    (candidate target : Coordinate → Int)
    (i : Coordinate)
    (seen : i ∈ targeted)
    (changed : candidate i ≠ target i) :
    ¬ MathCan.NOR23CoordinateAudit.agreesOn
        (targeted ++ randomReserve) candidate target := by
  exact MathCan.NOR23CoordinateAudit.checked_disagreement_definitively_rejects
    (targeted ++ randomReserve) candidate target i
    (List.mem_append.mpr (Or.inl seen)) changed

/-- The zero-security limit of revealing the realized complete schedule:
any still-unchecked coordinate allows a distinct output with the SAME
full ordered exact-value transcript. This is constructive in the model. -/
theorem schedule_visible_attacker_has_identical_transcript
    (checked : List Coordinate)
    (target : Coordinate → Int)
    (blindSpot : ∃ i : Coordinate, i ∉ checked) :
    ∃ altered : Coordinate → Int,
      altered ≠ target ∧
      MathCan.NOR24SequentialWitness.readTranscript checked target =
        MathCan.NOR24SequentialWitness.readTranscript checked altered := by
  obtain ⟨altered, distinct, identicalOnChecked⟩ :=
    MathCan.NOR23CoordinateAudit.adaptive_attacker_has_undetected_alternate_future
      checked target blindSpot
  refine ⟨altered, distinct, ?_⟩
  exact MathCan.NOR24SequentialWitness.checked_equal_targets_have_equal_transcripts
    checked target altered identicalOnChecked

#print axioms exact_two_stage_blind_count
#print axioms targeted_detection_is_certain
#print axioms uniform_reserve_miss_count_bounded
#print axioms extending_inspections_preserves_rejection
#print axioms inspected_targeted_change_is_detected
#print axioms schedule_visible_attacker_has_identical_transcript

end MathCan.NOR25UniformReserve
