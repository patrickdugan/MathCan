import MathCan.NOR29EarlyEntropyGame

/-!
# NOR-31: matched-restart attack games with independent calibration roots

NOR-29's finite bound compares a root-specific optimal attack to one
fixed in advance. NOR-31 adds a fresh calibration-root variable and
an explicit matched finite collection of optimizer tie seeds.

Each calibration root c and restart tie t produces a fixed attack
calibrated(c,t), chosen before the unknown evaluation root e.
A root-aware best response optimal(e,t) may depend on the realized
evaluation root. The batch loss counts detections across ALL 512
schedules determined by that root, with one attack fixed per batch.

If optimal(e,t) minimizes batch loss pointwise over attack choices,
then summing across any finite Cartesian product of calibration roots,
evaluation roots and restart ties gives a lower/equal total to the
root-aware attack. This holds even when the same set of tie seeds is
used for both strategies. The theorem is structural, conditional on
global optimality; a greedy heuristic may fail to find the optimum,
so the observed NOR-31 win count is a separately registered experiment.

The exact two-root witness remains strict for any independent
calibration strategy, while a deliberately poor root-aware rule can
lose to a precommitted fixed attack. SHA binding and authentic target
witnesses remain outside this theorem.
-/

namespace MathCan.NOR31MatchedRootCalibration

universe u v w z

open MathCan.NOR29EarlyEntropyGame

/-- Total detections when one independently selected pre-root attack is
held fixed across the actual audit batch, summed over independent
calibration roots and matched tie-restart choices. -/
def calibrationBatchLoss
    {Calibration : Type u} {Root : Type v}
    {Tie : Type w} {Attack : Type z}
    (calRoots : List Calibration) (roots : List Root) (ties : List Tie)
    (runs : Root → List (Attack → Nat))
    (calibrated : Calibration → Tie → Attack) : Nat :=
  (calRoots.map (fun c =>
    (ties.map (fun t =>
      precommitDetected roots runs (calibrated c t))).sum)).sum

/-- Total detections after the actual evaluation root is disclosed
before the attacker selects one attack for its entire audit batch.
Each restart uses the SAME tie values as the independent arm. -/
def disclosedRootBatchLoss
    {Calibration : Type u} {Root : Type v}
    {Tie : Type w} {Attack : Type z}
    (calRoots : List Calibration) (roots : List Root) (ties : List Tie)
    (runs : Root → List (Attack → Nat))
    (aware : Root → Tie → Attack) : Nat :=
  (calRoots.map (fun _ =>
    (ties.map (fun t =>
      leakedRootDetected roots runs (fun r => aware r t))).sum)).sum

/-- The finite min-expectation information inequality remains true
after adding an independent calibration root and matching every
optimizer tie seed, provided the disclosed-root strategy chooses a
batch-optimal attack under each evaluation root. -/
theorem globally_optimal_leaked_root_dominates_matched_calibration
    {Calibration : Type u} {Root : Type v}
    {Tie : Type w} {Attack : Type z}
    (calRoots : List Calibration) (roots : List Root) (ties : List Tie)
    (runs : Root → List (Attack → Nat))
    (calibrated : Calibration → Tie → Attack)
    (aware : Root → Tie → Attack)
    (hoptimal : ∀ (r : Root) (t : Tie) (a : Attack),
      batchDetected runs r (aware r t) ≤ batchDetected runs r a) :
    disclosedRootBatchLoss calRoots roots ties runs aware ≤
      calibrationBatchLoss calRoots roots ties runs calibrated := by
  have perCalibration (c : Calibration) :
      (ties.map (fun t =>
        leakedRootDetected roots runs (fun r => aware r t))).sum ≤
      (ties.map (fun t =>
        precommitDetected roots runs (calibrated c t))).sum := by
    induction ties with
    | nil => simp
    | cons t rest ih =>
        simp only [List.map_cons, List.sum_cons]
        apply Nat.add_le_add
        · exact optimal_leaked_root_response_dominates_precommit
            roots runs (fun r => aware r t) (calibrated c t)
            (by intro r; exact hoptimal r t (calibrated c t))
        · exact ih
  induction calRoots with
  | nil =>
      simp [disclosedRootBatchLoss, calibrationBatchLoss]
  | cons c rest ih =>
      simp only [disclosedRootBatchLoss, calibrationBatchLoss,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add (perCalibration c) ih

/-- For a Boolean two-root/two-coordinate audit game, every
calibration-only fixed attack is caught once across the two evaluation
roots, and a root-aware attacker always changes the uninspected
coordinate, even with matched restarts. -/
theorem strict_matched_calibration_two_root_game
    (calibrated : Bool → Bool → Bool) :
    disclosedRootBatchLoss
        [false,true] [false,true] [false,true]
        twoWorldRuns (fun r _ => avoidKnownRoot r) <
      calibrationBatchLoss
        [false,true] [false,true] [false,true]
        twoWorldRuns calibrated := by
  have hzero := root_aware_two_worlds_zero_detection
  have hone (a : Bool) := fixed_blind_two_worlds_one_detection a
  simp [disclosedRootBatchLoss, calibrationBatchLoss,
    hzero, hone]

/-- Independence of the precommit choice from the actual root is
represented by its function signature. For fixed calibration and
tie values, the selected attack is the same for all roots. -/
theorem fixed_calibrated_attack_ignores_eval_root
    {Calibration : Type u} {Root : Type v}
    {Tie : Type w} {Attack : Type z}
    (calibrated : Calibration → Tie → Attack)
    (c : Calibration) (t : Tie) (_e₁ _e₂ : Root) :
    calibrated c t = calibrated c t := by
  rfl

/-- Root-aware algorithms that do not find an optimum need not beat
blind policies. A deliberately poor leaked-root rule chooses the
INSPECTED coordinate in the two-root example and is caught twice. -/
def poorKnownRootChoice (root : Bool) : Bool := root

theorem nonoptimal_root_aware_can_lose
    (fixed : Bool) :
    precommitDetected [false,true] twoWorldRuns fixed <
      leakedRootDetected [false,true] twoWorldRuns poorKnownRootChoice := by
  cases fixed <;> decide

/-- An altered post-root attack cannot reopen the source's earlier
digest under the abstract binding hypothesis imported from NOR-28. -/
theorem new_root_aware_support_requires_new_binding
    {Salt : Type u} {Attack : Type v} {Digest : Type w}
    (commit : Salt → Attack → Digest)
    (binding : MathCan.NOR28CommitBeforeEntropy.AttackBinding commit)
    (saltOld saltNew : Salt) (oldAttack lateAttack : Attack)
    (different : oldAttack ≠ lateAttack) :
    commit saltOld oldAttack ≠ commit saltNew lateAttack := by
  exact MathCan.NOR28CommitBeforeEntropy.changed_attack_cannot_open_old_commitment
    commit binding saltOld saltNew oldAttack lateAttack different

#print axioms globally_optimal_leaked_root_dominates_matched_calibration
#print axioms strict_matched_calibration_two_root_game
#print axioms fixed_calibrated_attack_ignores_eval_root
#print axioms nonoptimal_root_aware_can_lose
#print axioms new_root_aware_support_requires_new_binding

end MathCan.NOR31MatchedRootCalibration
