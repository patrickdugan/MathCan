import MathCan.NOR22ModularFutureCommitments

/-!
# NOR-23: exact coordinate witnesses, finite binomial sampling, and evasion

This standalone Lean 4.35 proof uses the MathCan core toolchain with
no external Mathlib dependency. Exact target values at sampled coordinates
are an *extra authentic witness*, not implied by observation program evidence.

For n indexed coordinates, counting every k-position selection path by a
self-contained recursive enumeration gives the binomial recurrence.
A Boolean attack mask partitions n coordinates into r altered and n-r
unaltered positions. Hence exact undetected k-subset count is C(n-r,k),
and all k-subset count is C(n,k). For uniform sampling independently
after a fixed attack, the ratio is the exact miss probability. Sampling
assumptions and witness authenticity lie outside this Lean model.
-/

namespace MathCan.NOR23CoordinateAudit

universe u v
variable {Coordinate : Type u} {Public : Type v}

/-- An honest external target witness agrees with the proposed output
    on each coordinate checked by the auditor. -/
def agreesOn (checked : List Coordinate)
    (candidate target : Coordinate → Int) : Prop :=
  ∀ i ∈ checked, candidate i = target i

/-- One inspected discrepancy conclusively rejects exact target equality. -/
theorem checked_disagreement_definitively_rejects
    (checked : List Coordinate)
    (candidate target : Coordinate → Int)
    (i : Coordinate) (hi : i ∈ checked)
    (different : candidate i ≠ target i) :
    ¬ agreesOn checked candidate target := by
  intro h
  exact different (h i hi)

/-- Agreement on a larger set of inspected coordinates entails agreement
    on every smaller inspected coordinate roster. -/
theorem audit_agreement_monotone
    (small big : List Coordinate)
    (candidate target : Coordinate → Int)
    (subset : ∀ i ∈ small, i ∈ big)
    (hagrees : agreesOn big candidate target) :
    agreesOn small candidate target := by
  intro i hi
  exact hagrees i (subset i hi)

/-- If the audit roster covers the entire finite coordinate type,
    checking every listed coefficient is exact full target equality. -/
theorem complete_exact_audit_iff_target_equality
    (all : List Coordinate)
    (covers : ∀ i : Coordinate, i ∈ all)
    (candidate target : Coordinate → Int) :
    agreesOn all candidate target ↔ candidate = target := by
  constructor
  · intro h
    funext i
    exact h i (covers i)
  · intro h
    subst target
    intro i _
    rfl

/-- Any unchecked coordinate permits a distinct hidden future that
    passes every reported exact coordinate comparison. -/
theorem invisible_single_coordinate_override
    (checked : List Coordinate)
    (original : Coordinate → Int)
    (j : Coordinate) (unseen : j ∉ checked) :
    ∃ altered : Coordinate → Int,
      altered ≠ original ∧ agreesOn checked original altered := by
  classical
  let altered : Coordinate → Int :=
    fun i => if i = j then original i + 1 else original i
  refine ⟨altered, ?_, ?_⟩
  · intro same
    have h : altered j = original j := congrFun same j
    have heq : original j + 1 = original j := by
      simpa [altered] using h
    omega
  · intro i hi
    have hij : i ≠ j := by
      intro h
      exact unseen (h ▸ hi)
    change original i = altered i
    simp [altered, hij]

/-- An adaptive attacker that can select any unchecked coordinate
    always has a modified target compatible with the same witness. -/
theorem adaptive_attacker_has_undetected_alternate_future
    (checked : List Coordinate)
    (original : Coordinate → Int)
    (hasBlindSpot : ∃ j : Coordinate, j ∉ checked) :
    ∃ altered : Coordinate → Int,
      altered ≠ original ∧ agreesOn checked original altered := by
  obtain ⟨j, hj⟩ := hasBlindSpot
  exact invisible_single_coordinate_override checked original j hj

/-- The target-independent observation observer sees exact integer values
    only at audited coordinates; other positions return no value. -/
noncomputable def revealedCoordinates
    (checked : List Coordinate)
    (target : Coordinate → Int) : Coordinate → Option Int := by
  classical
  exact fun i => if i ∈ checked then some (target i) else none

/-- Two targets that agree at sampled coordinates have the same entire
    target-witness transcript, including inaccessible positions. -/
theorem identical_audit_transcripts_of_checked_agreement
    (checked : List Coordinate)
    (a b : Coordinate → Int)
    (hagrees : agreesOn checked a b) :
    revealedCoordinates checked a = revealedCoordinates checked b := by
  classical
  funext i
  by_cases hi : i ∈ checked
  · simp [revealedCoordinates, hi, hagrees i hi]
  · simp [revealedCoordinates, hi]

/-- Public-and-sampled-data observers cannot give two different exact
    hidden answers to two observationally identical worlds. -/
theorem identical_public_and_partial_witness_worlds
    (checked : List Coordinate)
    (selector : (Public × (Coordinate → Option Int)) →
      Option (Coordinate → Int))
    (observation : Public)
    (a b : Coordinate → Int)
    (hagrees : agreesOn checked a b)
    (different : a ≠ b) :
    selector (observation, revealedCoordinates checked a) ≠ some a ∨
      selector (observation, revealedCoordinates checked b) ≠ some b := by
  have same :=
    identical_audit_transcripts_of_checked_agreement checked a b hagrees
  rw [← same]
  exact MathCan.NOR21ObservationCompleteness.identical_public_worlds_cannot_both_be_future_correct
    selector (observation, revealedCoordinates checked a) a b different

/-- A self-contained binomial coefficient recurrence for choosing k
    positions out of n, including out-of-range k>n. -/
def binomial : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => binomial n k + binomial n (k + 1)

/-- Exhaustive k-position choices from a list. Repeated Boolean values
    can yield duplicate value-lists, but each enumeration path selects
    a distinct subset of original coordinate positions. -/
def kSubsets {α : Type u} : List α → Nat → List (List α)
  | [], 0 => [[]]
  | [], _ + 1 => []
  | _ :: _, 0 => [[]]
  | x :: xs, k + 1 =>
      (kSubsets xs k).map (fun ys => x :: ys) ++ kSubsets xs (k + 1)

/-- Every k-position selection path is counted by the binomial
    recurrence, proved by list induction without library combinatorics. -/
theorem k_subset_count_is_binomial {α : Type u}
    (xs : List α) (k : Nat) :
    (kSubsets xs k).length = binomial xs.length k := by
  induction xs generalizing k with
  | nil =>
      cases k <;> rfl
  | cons x xs ih =>
      cases k with
      | zero =>
          rfl
      | succ k =>
          simp [kSubsets, binomial, ih]

/-- A target alteration mask partitions positions into changed and
    unchanged coordinates, exactly accounting for all positions. -/
theorem changed_unchanged_partition_counts (mask : List Bool) :
    (mask.filter (fun b => !b)).length +
      (mask.filter (fun b => b)).length = mask.length := by
  induction mask with
  | nil => rfl
  | cons b rest ih =>
      cases b <;> simp [List.filter] at ih ⊢ <;> omega

/-- Every possible k-coordinate audit drawn from n positions has
    binomial(n,k) possibilities (input positions are distinct). -/
theorem total_k_coordinate_challenges
    (mask : List Bool) (k : Nat) :
    (kSubsets mask k).length = binomial mask.length k := by
  exact k_subset_count_is_binomial mask k

/-- For a FIXED Boolean alteration mask, all k-subsets that only choose
    unchanged coordinates number exactly binomial(n-r,k). No randomness
    is assumed in this finite counting identity. -/
theorem fixed_attack_undetected_challenge_count
    (mask : List Bool) (k : Nat) :
    (kSubsets (mask.filter (fun b => !b)) k).length =
      binomial (mask.length - (mask.filter (fun b => b)).length) k := by
  have partition := changed_unchanged_partition_counts mask
  have hlen :
      (mask.filter (fun b => !b)).length =
        mask.length - (mask.filter (fun b => b)).length := by
    omega
  calc
    (kSubsets (mask.filter (fun b => !b)) k).length =
        binomial (mask.filter (fun b => !b)).length k :=
          k_subset_count_is_binomial _ _
    _ = binomial (mask.length - (mask.filter (fun b => b)).length) k := by
      rw [hlen]

/-- The numerator and denominator counts yield the exact combinatorial
    miss ratio C(n-r,k)/C(n,k) for a blind fixed-r attack. A uniform
    sample over k-subsets is required to read the ratio as probability. -/
theorem exact_hypergeometric_miss_pair
    (mask : List Bool) (k : Nat) :
    ((kSubsets (mask.filter (fun b => !b)) k).length,
     (kSubsets mask k).length) =
    (binomial (mask.length - (mask.filter (fun b => b)).length) k,
     binomial mask.length k) := by
  rw [fixed_attack_undetected_challenge_count,
      total_k_coordinate_challenges]

#print axioms checked_disagreement_definitively_rejects
#print axioms audit_agreement_monotone
#print axioms complete_exact_audit_iff_target_equality
#print axioms invisible_single_coordinate_override
#print axioms adaptive_attacker_has_undetected_alternate_future
#print axioms identical_audit_transcripts_of_checked_agreement
#print axioms identical_public_and_partial_witness_worlds
#print axioms k_subset_count_is_binomial
#print axioms changed_unchanged_partition_counts
#print axioms total_k_coordinate_challenges
#print axioms fixed_attack_undetected_challenge_count
#print axioms exact_hypergeometric_miss_pair

end MathCan.NOR23CoordinateAudit
