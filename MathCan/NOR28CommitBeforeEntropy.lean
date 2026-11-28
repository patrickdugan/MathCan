import MathCan.NOR27SeedLeakage

/-!
# NOR-28: irrevocable attack commitment before audit entropy

An authentic exact target witness detects a changed coordinate if and only if
its inspected set intersects the altered support, under the declared
nonzero-change model. A *binding* attack commitment is fixed before
fresh audit random coins are generated. Any subsequently disclosed function
of those coins is observational side-information and cannot change the
already committed attack support. The detection decision for a fixed full
schedule is therefore unchanged across every postcommit disclosure view.

Commitment binding is formalized as an abstract hypothesis on a hash-like
function over attacker salt and altered positions. Lean proves the logical
consequences of that assumption, not SHA256 collision resistance. An attacker
that can create a new commitment after seeing the complete inspection set can
instead select an unchecked coordinate and preserve the same exact-value
witness transcript. This separates protocol chronology from the amount of
randomness disclosed.

NOR-25 and NOR-26 separately prove the exact missed-sample count for
a fixed blind attack under a uniform reserve. The present module connects
that finite bound to a binding attack-choice relation.
-/

namespace MathCan.NOR28CommitBeforeEntropy

universe u v w z

/-- An attack must be bound by its commitment digest independently of
the randomized root and later transcript disclosure.  Salt collisions on
identical attacks are harmless; cross-attack collisions are excluded. -/
def AttackBinding {Salt : Type u} {Attack : Type v} {Digest : Type w}
    (commit : Salt → Attack → Digest) : Prop :=
  ∀ (salt₁ salt₂ : Salt) (attack₁ attack₂ : Attack),
    commit salt₁ attack₁ = commit salt₂ attack₂ → attack₁ = attack₂

/-- If a post-disclosure attacker supplies an opening with the same
original commitment, its attack support must be unchanged. -/
theorem same_digest_forces_original_attack
    {Salt : Type u} {Attack : Type v} {Digest : Type w}
    (commit : Salt → Attack → Digest)
    (binding : AttackBinding commit)
    (salt₁ salt₂ : Salt) (original replacement : Attack)
    (opens : commit salt₁ original = commit salt₂ replacement) :
    original = replacement :=
  binding salt₁ salt₂ original replacement opens

/-- Any genuinely changed attack support fails to open the old digest
under the abstract commitment-binding hypothesis. -/
theorem changed_attack_cannot_open_old_commitment
    {Salt : Type u} {Attack : Type v} {Digest : Type w}
    (commit : Salt → Attack → Digest)
    (binding : AttackBinding commit)
    (salt₁ salt₂ : Salt) (original replacement : Attack)
    (changed : original ≠ replacement) :
    commit salt₁ original ≠ commit salt₂ replacement := by
  intro equalCommitment
  exact changed (same_digest_forces_original_attack
    commit binding salt₁ salt₂ original replacement equalCommitment)

/-- Exact-coordinate detection of a changed support by a checked roster.
An actual witness is needed to establish which coefficients differ. -/
def detects {Coordinate : Type u}
    (checked changed : List Coordinate) : Prop :=
  ∃ i, i ∈ checked ∧ i ∈ changed

/-- An auditor's complete realized inspection set depends on the root.
The committed attack remains fixed, and a later disclosed leakage view
is deliberately irrelevant to its already determined intersection. -/
def postCommitDetection
    {Root : Type u} {Coordinate : Type v} {Leak : Type w}
    (schedule : Root → List Coordinate)
    (committedAttack : List Coordinate)
    (root : Root) (_revealed : Leak) : Prop :=
  detects (schedule root) committedAttack

/-- For any two functions disclosing information about the actual
random root *after commitment*, the same attack and schedule produce
the same exact intersection result. This is pathwise, not an average. -/
theorem disclosure_after_commitment_cannot_change_detection
    {Root : Type u} {Coordinate : Type v} {Leak₁ : Type w} {Leak₂ : Type z}
    (schedule : Root → List Coordinate)
    (originalAttack : List Coordinate)
    (root : Root)
    (disclose₁ : Root → Leak₁) (disclose₂ : Root → Leak₂) :
    postCommitDetection schedule originalAttack root (disclose₁ root) ↔
      postCommitDetection schedule originalAttack root (disclose₂ root) := by
  rfl

/-- Even an attacker who knows the entire newly sampled root can only
submit the originally committed attack under abstract binding. Its
detected coordinates coincide with those of the first opening. -/
theorem binding_preserves_detection_under_reopening
    {Salt : Type u} {Attack : Type v} {Digest : Type w}
    (commit : Salt → Attack → Digest)
    (binding : AttackBinding commit)
    (salt₁ salt₂ : Salt) (original replacement : Attack)
    (opens : commit salt₁ original = commit salt₂ replacement)
    (isDetected : Attack → Prop) :
    isDetected original ↔ isDetected replacement := by
  have h : original = replacement :=
    same_digest_forces_original_attack
      commit binding salt₁ salt₂ original replacement opens
  rw [h]

/-- If a partial audit leaves an uninspected coordinate and the
attacker can choose its alteration after the schedule is known,
the opponent can construct a changed future with an identical
ordered exact-value witness transcript. -/
theorem new_commitment_after_schedule_allows_evasion
    {Coordinate : Type u}
    (inspected : List Coordinate)
    (target : Coordinate → Int)
    (unseen : ∃ i : Coordinate, i ∉ inspected) :
    ∃ changed : Coordinate → Int,
      changed ≠ target ∧
      MathCan.NOR24SequentialWitness.readTranscript inspected target =
        MathCan.NOR24SequentialWitness.readTranscript inspected changed := by
  exact MathCan.NOR25UniformReserve.schedule_visible_attacker_has_identical_transcript
    inspected target unseen

/-- The previously proved uniform-reserve mixture floor is retained
for any roster of residual worlds with a fixed blind attack. The
positive floor is a combinatorial statement conditional on ideal
independent uniform sampling, not on the cryptographic hash function. -/
theorem bound_persists_for_bound_attack
    (N r reserve : Nat)
    (worlds : List MathCan.NOR26PolicyAwareBlindAudit.PrefixOutcome)
    (valid : ∀ p ∈ worlds,
      MathCan.NOR26PolicyAwareBlindAudit.fixedBlindRadius N r p) :
    MathCan.NOR26PolicyAwareBlindAudit.totalMisses worlds reserve ≤
      worlds.length *
        MathCan.NOR23CoordinateAudit.binomial (N-r) reserve := by
  exact MathCan.NOR26PolicyAwareBlindAudit.policy_aware_fixed_attack_mixture_bound
    N r reserve worlds valid

#print axioms same_digest_forces_original_attack
#print axioms changed_attack_cannot_open_old_commitment
#print axioms disclosure_after_commitment_cannot_change_detection
#print axioms binding_preserves_detection_under_reopening
#print axioms new_commitment_after_schedule_allows_evasion
#print axioms bound_persists_for_bound_attack

end MathCan.NOR28CommitBeforeEntropy
