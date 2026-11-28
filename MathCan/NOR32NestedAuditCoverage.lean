import MathCan.NOR31MatchedRootCalibration

/-!
# NOR-32: nested batch audit coverage, four-coordinate feasibility and loss

At stage n, an auditor reveals the first n check lists of one fixed
root-derived sequence. The union of inspected positions grows as n grows;
equivalently the coordinates never inspected by any check shrink. If one
radius-four altered set evades all checks in a LONGER batchStart, it also evades
every check in the SHORTER batchStart. Feasibility of a completely missed batch
cannot reappear after it is lost. These finite logical statements are fully
independent of the randomness generator.

For each fixed attack, the TOTAL number of detected checks is monotone
as a sequence is extended, because every appended nonnegative detection
cost is added to the old count. The MINIMUM total detection count over a
fixed attack menu cannot decrease as a corollary. Conversely, detection as
a FRACTION of challenges need not increase: a single hit out of one scan
becomes one hit out of two if the second scan misses the attack.

The ideal-uniform expectation of still unseen risk-free coordinates is
N*(1-u/N)^n (N=m-8, u=8); that probabilistic calculation and Markov's
bound Pr(unseen>=r) <= E[unseen]/r are described in the companion paper.
The Lean module proves finite protocol/coverage structure, with OS entropy,
SHA binding, HMAC PRF, and true exact-value witness as external assumptions.
-/

namespace MathCan.NOR32NestedAuditCoverage

universe u v

/-- One alteration support evades an entire finite audit roster if it
shares no changed coordinate with any inspected check list. -/
def evadesBatch {Coordinate : Type u}
    (plans : List (List Coordinate)) (attack : List Coordinate) : Prop :=
  ∀ plan ∈ plans,
    ¬ MathCan.NOR28CommitBeforeEntropy.detects plan attack

/-- Every alteration that evades an appended batch also evades both
sub-batches. Append decomposition is exact for finite inspection lists. -/
theorem evades_append_iff
    {Coordinate : Type u}
    (batchStart suffix : List (List Coordinate))
    (attack : List Coordinate) :
    evadesBatch (batchStart ++ suffix) attack ↔
      evadesBatch batchStart attack ∧ evadesBatch suffix attack := by
  constructor
  · intro h
    constructor
    · intro plan hp
      exact h plan (List.mem_append.mpr (Or.inl hp))
    · intro plan hp
      exact h plan (List.mem_append.mpr (Or.inr hp))
  · intro h plan hp
    rcases List.mem_append.mp hp with inPrefix | inSuffix
    · exact h.1 plan inPrefix
    · exact h.2 plan inSuffix

/-- A specific coordinate is untouched if every check in the batch
avoids it, including checks introduced by the trained-risk batchStart. -/
def neverInspected {Coordinate : Type u}
    (plans : List (List Coordinate)) (i : Coordinate) : Prop :=
  ∀ plan ∈ plans, i ∉ plan

theorem never_inspected_at_longer_depth_was_unseen_earlier
    {Coordinate : Type u}
    (earlier extra : List (List Coordinate)) (i : Coordinate)
    (h : neverInspected (earlier ++ extra) i) :
    neverInspected earlier i := by
  intro plan hp
  exact h plan (List.mem_append.mpr (Or.inl hp))

/-- Feasibility means that FOUR distinct altered positions can remain
unchanged in the exact target while every inspected coefficient matches. -/
def fourCoordinateBatchEvasionFeasible {Coordinate : Type u}
    (plans : List (List Coordinate)) : Prop :=
  ∃ attack : List Coordinate,
    attack.Nodup ∧ attack.length = 4 ∧ evadesBatch plans attack

/-- Once the batch has sampled enough coordinates to make four
never-inspected indices impossible, extending the audit can never restore
the four-coordinate zero-detection attack. -/
theorem four_coordinate_evasion_feasibility_monotone
    {Coordinate : Type u}
    (earlier extra : List (List Coordinate))
    (h : fourCoordinateBatchEvasionFeasible (earlier ++ extra)) :
    fourCoordinateBatchEvasionFeasible earlier := by
  rcases h with ⟨attack, distinct, radius, evades⟩
  exact ⟨attack, distinct, radius,
    (evades_append_iff earlier extra attack).mp evades |>.1⟩

theorem impossible_four_coordinate_evasion_stays_impossible
    {Coordinate : Type u}
    (earlier extra : List (List Coordinate))
    (h : ¬ fourCoordinateBatchEvasionFeasible earlier) :
    ¬ fourCoordinateBatchEvasionFeasible (earlier ++ extra) := by
  intro possible
  exact h (four_coordinate_evasion_feasibility_monotone
    earlier extra possible)

/-- Total nonnegative detection counts for an attack fixed across an
entire batch, allowing arbitrary scoring losses as long as they are Nat. -/
def totalBatchLoss {Scan : Type u} {Attack : Type v}
    (checks : List Scan) (loss : Scan → Attack → Nat) (attack : Attack) : Nat :=
  (checks.map (fun scan => loss scan attack)).sum

theorem total_batch_loss_append
    {Scan : Type u} {Attack : Type v}
    (batchStart suffix : List Scan)
    (loss : Scan → Attack → Nat) (attack : Attack) :
    totalBatchLoss (batchStart ++ suffix) loss attack =
      totalBatchLoss batchStart loss attack +
        totalBatchLoss suffix loss attack := by
  simp [totalBatchLoss, List.map_append, List.sum_append]

/-- Adding audits cannot decrease the ABSOLUTE detection count of
any fixed altered support, regardless of how the source was sampled. -/
theorem total_detection_count_monotone_under_nested_audits
    {Scan : Type u} {Attack : Type v}
    (batchStart suffix : List Scan)
    (loss : Scan → Attack → Nat) (attack : Attack) :
    totalBatchLoss batchStart loss attack ≤
      totalBatchLoss (batchStart ++ suffix) loss attack := by
  rw [total_batch_loss_append]
  omega

/-- A lower bound that holds for EVERY attack in a fixed menu persists
when additional checks are appended. It follows that the minimum total
hit count across this fixed menu cannot decrease as the batch grows. -/
theorem any_menu_lower_bound_survives_extra_audits
    {Scan : Type u} {Attack : Type v}
    (menu : List Attack) (batchStart suffix : List Scan)
    (loss : Scan → Attack → Nat) (lower : Nat)
    (h : ∀ attack ∈ menu, lower ≤ totalBatchLoss batchStart loss attack) :
    ∀ attack ∈ menu,
      lower ≤ totalBatchLoss (batchStart ++ suffix) loss attack := by
  intro attack inMenu
  exact Nat.le_trans (h attack inMenu)
    (total_detection_count_monotone_under_nested_audits batchStart suffix loss attack)

/-- A concrete counterexample: a fixed attack is caught on the first
audit and not on the second. Its hit RATE drops from 1/1 to 1/2
although the absolute hit count stays at one. -/
def toyLoss (scan : Bool) (_attack : Unit) : Nat :=
  if scan then 1 else 0

theorem detection_fraction_need_not_increase :
    2 * totalBatchLoss [true] toyLoss () >
      totalBatchLoss [true,false] toyLoss () := by
  decide

#print axioms evades_append_iff
#print axioms never_inspected_at_longer_depth_was_unseen_earlier
#print axioms four_coordinate_evasion_feasibility_monotone
#print axioms impossible_four_coordinate_evasion_stays_impossible
#print axioms total_batch_loss_append
#print axioms total_detection_count_monotone_under_nested_audits
#print axioms any_menu_lower_bound_survives_extra_audits
#print axioms detection_fraction_need_not_increase

end MathCan.NOR32NestedAuditCoverage
