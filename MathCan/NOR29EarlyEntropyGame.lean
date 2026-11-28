import MathCan.NOR28CommitBeforeEntropy

/-!
# NOR-29: the finite advantage of observing audit entropy before commitment

A protocol that binds the attack before the audit root is sampled forces one
attack across all possible root worlds. If the root is disclosed first,
the attacker may choose a different batch-fixed attack for each root, while
holding that chosen attack constant across every schedule within its batch.

For a finite roster of root worlds, the pointwise-minimal batch response has
sum of losses no larger than any fixed pre-root choice. The inequality can
be strict even though the same attacker still uses one fixed attack within
each root's batch. This is the min-expectation gap E[min] ≤ min E.

An explicit two-root counterexample has one audit probe and two possible
changed locations. Each fixed attack is detected in exactly one world,
while the seed-aware attacker always selects the uninspected location.

The separate information regime of choosing a different attack after each
individual audit is captured by the no-hit iff all altered coordinates avoid
every inspected set. The existing NOR-28 abstract commitment-binding theorem
prevents the attacker from re-opening the old digest with a late new attack,
subject to the binding assumption. Nothing in this module proves SHA-256
security, OS entropy quality, or HMAC unpredictability.
-/

namespace MathCan.NOR29EarlyEntropyGame

universe u v w

/-- A root specifies an entire audit batch. This sum is the number of
detected altered outputs across the scheduled audits with one fixed A. -/
def batchDetected {Root : Type u} {Attack : Type v}
    (runs : Root → List (Attack → Nat))
    (root : Root) (attack : Attack) : Nat :=
  ((runs root).map (fun check => check attack)).sum

/-- If the root becomes visible before binding an attack, the
attacker can adapt to that root while fixing A over the full batch. -/
def leakedRootDetected {Root : Type u} {Attack : Type v}
    (roots : List Root) (runs : Root → List (Attack → Nat))
    (choose : Root → Attack) : Nat :=
  (roots.map (fun root => batchDetected runs root (choose root))).sum

/-- A pre-root-binding attacker uses a single attack for every root. -/
def precommitDetected {Root : Type u} {Attack : Type v}
    (roots : List Root) (runs : Root → List (Attack → Nat))
    (fixed : Attack) : Nat :=
  (roots.map (fun root => batchDetected runs root fixed)).sum

/-- Once an attacker is allowed to choose an attack for each root,
its total number of detected batches is at most that of ANY fixed attack,
provided the root-conditional choice minimizes each full batch. -/
theorem optimal_leaked_root_response_dominates_precommit
    {Root : Type u} {Attack : Type v}
    (roots : List Root) (runs : Root → List (Attack → Nat))
    (choose : Root → Attack) (fixed : Attack)
    (hbest : ∀ root : Root,
      batchDetected runs root (choose root) ≤
        batchDetected runs root fixed) :
    leakedRootDetected roots runs choose ≤
      precommitDetected roots runs fixed := by
  induction roots with
  | nil =>
      simp [leakedRootDetected, precommitDetected]
  | cons root rest ih =>
      simp only [leakedRootDetected, precommitDetected,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hbest root) ih

/-- Applied calibration optimization only needs an upper-bound
candidate, since early disclosure enlarges the available attack strategy
set. Using the same fixed precommit attack remains permissible. -/
theorem fixed_attack_is_a_root_aware_strategy
    {Root : Type u} {Attack : Type v}
    (roots : List Root) (runs : Root → List (Attack → Nat))
    (fixed : Attack) :
    leakedRootDetected roots runs (fun _ => fixed) =
      precommitDetected roots runs fixed := by
  rfl

/-- Simplest two-root example: a single audit checks the root's bit.
An attack changes that same indexed bit if its Boolean value matches. -/
def oneProbeDetects (root altered : Bool) : Nat :=
  if root == altered then 1 else 0

/-- Each possible root has one authentic audit of a single coordinate. -/
def twoWorldRuns (root : Bool) : List (Bool → Nat) :=
  [fun altered => oneProbeDetects root altered]

/-- The root-aware attacker chooses the other coordinate once per root. -/
def avoidKnownRoot (root : Bool) : Bool := !root

/-- A late attacker escapes both root worlds while holding its chosen
attack fixed for the complete (one-element) batch in each root. -/
theorem root_aware_two_worlds_zero_detection :
    leakedRootDetected [false, true] twoWorldRuns avoidKnownRoot = 0 := by
  decide

/-- Every fixed early commitment is hit in precisely one of the
two possible roots. This is a strict timing counterexample. -/
theorem fixed_blind_two_worlds_one_detection (attack : Bool) :
    precommitDetected [false, true] twoWorldRuns attack = 1 := by
  cases attack <;> decide

theorem strict_early_entropy_information_advantage (fixed : Bool) :
    leakedRootDetected [false, true] twoWorldRuns avoidKnownRoot <
      precommitDetected [false, true] twoWorldRuns fixed := by
  cases fixed <;> decide

/-- A source-batch fixed attack evades every schedule exactly when all
its changed coordinates are absent from every schedule in that batch. -/
theorem batch_fixed_evasion_iff_every_coordinate_unchecked
    {Coordinate : Type u}
    (schedules : List (List Coordinate)) (attack : List Coordinate) :
    (∀ plan ∈ schedules,
      ¬ MathCan.NOR28CommitBeforeEntropy.detects plan attack) ↔
    (∀ index ∈ attack, ∀ plan ∈ schedules, index ∉ plan) := by
  constructor
  · intro noneHit index altered plan inBatch inspected
    exact noneHit plan inBatch ⟨index, inspected, altered⟩
  · intro avoids plan inBatch hit
    rcases hit with ⟨index, checked, altered⟩
    exact avoids index altered plan inBatch checked

/-- Any new root-aware batch attack that differs from the original
precommitted attack cannot reuse the old digest under the original
abstract commitment-binding assumption. -/
theorem late_root_attack_requires_new_commitment
    {Salt : Type u} {Attack : Type v} {Digest : Type w}
    (commit : Salt → Attack → Digest)
    (binding : MathCan.NOR28CommitBeforeEntropy.AttackBinding commit)
    (originalSalt leakedSalt : Salt)
    (oldAttack rootAwareAttack : Attack)
    (different : oldAttack ≠ rootAwareAttack) :
    commit originalSalt oldAttack ≠
      commit leakedSalt rootAwareAttack := by
  exact MathCan.NOR28CommitBeforeEntropy.changed_attack_cannot_open_old_commitment
    commit binding originalSalt leakedSalt oldAttack rootAwareAttack different

#print axioms optimal_leaked_root_response_dominates_precommit
#print axioms fixed_attack_is_a_root_aware_strategy
#print axioms root_aware_two_worlds_zero_detection
#print axioms fixed_blind_two_worlds_one_detection
#print axioms strict_early_entropy_information_advantage
#print axioms batch_fixed_evasion_iff_every_coordinate_unchecked
#print axioms late_root_attack_requires_new_commitment

end MathCan.NOR29EarlyEntropyGame
