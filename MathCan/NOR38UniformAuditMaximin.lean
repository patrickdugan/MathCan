import MathCan.NOR37RandomizedCurvature

/-!
NOR-38: global all-output uniform reserve, regular finite attack games,
and an unrestricted precommitted-support minimax ceiling.

An arbitrary defender distributes audit mass over fixed size-k subsets
of m output coordinates. Every such k-subset has the same number
C(m,r)-C(m-k,r) of changed r-subsets that it detects when the attacker
support is averaged uniformly. In a finite hit incidence matrix this
is a REGULAR ROW property. A finite double count implies some fixed
attack column has detection no larger than the common attack-average.
The globally uniform k-subset policy attains that same conditional
ratio against every fixed r-subset by exact hypergeometric counting.

The theorem explicitly assumes the finite incidence matrix's
column-versus-row double-count equality, which is a property of genuine
full-output k-versus-r subset incidence. It is *not* an assumption of
minimax optimality or of any particular algorithm learning an attacker.

An independently hidden whole-output uniform branch of positive mass
gives a detection floor against every fixed precommitted changed set.
The authentication and entropy hypotheses are external.
-/

namespace MathCan.NOR38UniformAuditMaximin

abbrev choose := MathCan.NOR23CoordinateAudit.binomial

/-- Every fixed k-coordinate audit intersects exactly this many of the
    C(m,r) possible r-coordinate attack supports in a complete domain. -/
def uniformAttackHitCount (m k r : Nat) : Nat :=
  choose m r - choose (m-k) r

/-- Concrete row regularity: for a fixed public Boolean checked-position
    mask, uniformly enumerating every radius-r altered support detects
    C(m,r)-C(m-k,r) supports, where m is mask length and k is the
    number of checked positions. This supplies the finite incidence
    row count used in the minimax double-count, directly from NOR23's
    exact subset enumeration and the mask partition identity. -/
theorem fixed_audit_has_exact_uniform_attack_hit_count
    (auditMask : List Bool) (r : Nat) :
    (MathCan.NOR23CoordinateAudit.kSubsets auditMask r).length -
      (MathCan.NOR23CoordinateAudit.kSubsets
        (auditMask.filter (fun checked => !checked)) r).length =
      uniformAttackHitCount auditMask.length
        (auditMask.filter (fun checked => checked)).length r := by
  have part :=
    MathCan.NOR23CoordinateAudit.changed_unchanged_partition_counts auditMask
  have complementLength :
      (auditMask.filter (fun checked => !checked)).length =
      auditMask.length - (auditMask.filter (fun checked => checked)).length := by
    omega
  rw [MathCan.NOR23CoordinateAudit.k_subset_count_is_binomial,
      MathCan.NOR23CoordinateAudit.k_subset_count_is_binomial]
  simp [uniformAttackHitCount, complementLength]

/-- An all-output uniform k-audit misses precisely the uniform
    unchanged-position subsets for a fixed altered Boolean mask. -/
theorem full_output_uniform_blind_miss_pair
    (mask : List Bool) (k : Nat) :
    ((MathCan.NOR23CoordinateAudit.kSubsets
        (mask.filter (fun b => !b)) k).length,
     (MathCan.NOR23CoordinateAudit.kSubsets mask k).length) =
    (choose (mask.length - (mask.filter (fun b => b)).length) k,
     choose mask.length k) := by
  exact MathCan.NOR23CoordinateAudit.exact_hypergeometric_miss_pair mask k

/-- Given nonnegative weights of audit paths, the total weighted
    incidences counted by ROW equal uniform-row-hit-count times mass. -/
theorem regular_rows_weighted_double_count
    (weights : List Nat) (m k r : Nat) :
    (weights.map (fun w => w * uniformAttackHitCount m k r)).sum =
      weights.sum * uniformAttackHitCount m k r := by
  induction weights with
  | nil => simp
  | cons w ws ih =>
    simp [List.sum_cons, ih, Nat.add_mul]

private theorem sum_lower_bound_of_pointwise_lower
    (xs : List Nat) (bound : Nat) :
    (∀ x ∈ xs, bound ≤ x) → xs.length * bound ≤ xs.sum := by
  induction xs with
  | nil =>
    intro _
    simp
  | cons x xs ih =>
    intro hall
    have hx : bound ≤ x := hall x (by simp)
    have hrest : ∀ y ∈ xs, bound ≤ y := by
      intro y hy
      exact hall y (by simp [hy])
    have ht := ih hrest
    simp only [List.length_cons, List.sum_cons, Nat.succ_mul]
    omega

/-- Any nonempty finite list of attack payoffs has a member at or
    below any integer upper bound on its arithmetic mean. This is
    the finite minimax averaging step, proved without a mixed-game
    optimizer or assuming that a greedy attack found the optimum. -/
theorem finite_attack_has_response_below_average
    (coverage : List Nat) (benchmark : Nat)
    (nonempty : coverage ≠ [])
    (averaged : coverage.sum ≤ coverage.length * benchmark) :
    ∃ attackHits, attackHits ∈ coverage ∧ attackHits ≤ benchmark := by
  apply Classical.byContradiction
  intro noAttack
  have hall : ∀ x ∈ coverage, benchmark + 1 ≤ x := by
    intro x hx
    by_cases le : x ≤ benchmark
    · exact False.elim (noAttack ⟨x,hx,le⟩)
    · omega
  have lower := sum_lower_bound_of_pointwise_lower
    coverage (benchmark + 1) hall
  have positiveLength : 0 < coverage.length := by
    cases coverage with
    | nil => contradiction
    | cons _ _ => simp
  have low : coverage.length * benchmark + coverage.length ≤ coverage.sum := by
    simpa [Nat.mul_add] using lower
  omega

/-- Exact unconditional upper ceiling for any policy in a finite
    regular size-k versus size-r attack game. The incidence double count
    means that summing column payoffs equals summing every weighted audit
    row's number of detected attack supports. With C(m,r) attack columns,
    some precommitted support scores at most the uniform benchmark. -/
theorem regular_game_has_attack_at_uniform_ceiling
    (m k r : Nat) (auditWeights attackCoverage : List Nat)
    (threshold : Nat)
    (numberOfAttacks :
      attackCoverage.length = choose m r)
    (positiveAttacks : 0 < choose m r)
    (exactIncidenceDoubleCount :
      attackCoverage.sum =
        (auditWeights.map
          (fun w => w * uniformAttackHitCount m k r)).sum)
    (uniformCeiling :
      auditWeights.sum * uniformAttackHitCount m k r ≤
        choose m r * threshold) :
    ∃ hits, hits ∈ attackCoverage ∧ hits ≤ threshold := by
  have nonempty : attackCoverage ≠ [] := by
    intro empty
    simp [empty] at numberOfAttacks
    omega
  have average : attackCoverage.sum ≤ attackCoverage.length * threshold := by
    rw [exactIncidenceDoubleCount, regular_rows_weighted_double_count]
    rw [numberOfAttacks]
    exact uniformCeiling
  exact finite_attack_has_response_below_average
    attackCoverage threshold nonempty average

/-- The exact count of newly covered attack supports in a mixed auditor.
    The first branch is a UNIFORM sample across ALL m output coordinates.
    A curvature branch can have any nonnegative detection count. -/
def globalUniformMixtureDetection
    (m k r uniformWeight totalWeight curvatureHits : Nat) : Nat :=
  uniformWeight * uniformAttackHitCount m k r +
    (totalWeight - uniformWeight) * curvatureHits

/-- Certified unconditional whole-output support floor against any
    attack fixed before independent hidden audit coins. -/
theorem global_uniform_reserve_has_all_output_floor
    (m k r uniformWeight totalWeight curvatureHits : Nat) :
    uniformWeight * uniformAttackHitCount m k r ≤
      globalUniformMixtureDetection
        m k r uniformWeight totalWeight curvatureHits := by
  simp [globalUniformMixtureDetection]

/-- A fixed four-coordinate attack can only have positive guaranteed
    coverage if there is some possible uniform-branch hit and its
    independent selection probability is strictly positive. -/
theorem global_exploration_strict_when_uniform_can_hit
    (m k r uniformWeight totalWeight curvatureHits : Nat)
    (positiveWeight : 0 < uniformWeight)
    (positiveHit : 0 < uniformAttackHitCount m k r) :
    0 < globalUniformMixtureDetection
      m k r uniformWeight totalWeight curvatureHits := by
  have h : 0 < uniformWeight * uniformAttackHitCount m k r :=
    Nat.mul_pos positiveWeight positiveHit
  exact Nat.lt_of_lt_of_le h
    (global_uniform_reserve_has_all_output_floor
      m k r uniformWeight totalWeight curvatureHits)

/-- Fixed universal trials do not prevent transcript collisions when
    the realized inspection schedule itself is exposed to an attacker. -/
theorem revealed_global_schedule_remains_evadable
    {Coordinate : Type}
    (inspected : List Coordinate) (target : Coordinate → Int)
    (hasUnchecked : ∃ i, i ∉ inspected) :
    ∃ modified : Coordinate → Int,
      modified ≠ target ∧
      MathCan.NOR24SequentialWitness.readTranscript inspected target =
      MathCan.NOR24SequentialWitness.readTranscript inspected modified := by
  exact MathCan.NOR25UniformReserve.schedule_visible_attacker_has_identical_transcript
    inspected target hasUnchecked

#print axioms fixed_audit_has_exact_uniform_attack_hit_count
#print axioms full_output_uniform_blind_miss_pair
#print axioms regular_rows_weighted_double_count
#print axioms finite_attack_has_response_below_average
#print axioms regular_game_has_attack_at_uniform_ceiling
#print axioms global_uniform_reserve_has_all_output_floor
#print axioms global_exploration_strict_when_uniform_can_hit
#print axioms revealed_global_schedule_remains_evadable

end MathCan.NOR38UniformAuditMaximin
