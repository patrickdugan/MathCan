import MathCan.NOR26PolicyAwareBlindAudit

/-!
# NOR-27: exact random-reserve coverage after leakage of inspected coordinates

NOR-26 allows a fixed attack chosen with knowledge of the public auditor.
NOR-27 distinguishes two *information structures*.

In a sample-output preview, the attacker learns the t public-risk checks
and ell of the actual uniform-reserve checks before selecting its attack.
All r altered positions avoid those revealed coordinates. The remaining
u-ell checks are independently uniform among N=m-t-ell unseen positions.
The number of reserve subsets that still miss every attack is then
C(N-r,u-ell), out of C(N,u-ell) possible continuations. At ell=u the
auditor has no additional randomness and every legal alteration remains
invisible. This exact count is proved here using NOR-23 and NOR-25.

A raw high-bit leak from a seed is weaker or stronger depending on the
seed-to-sample map. A deterministic attack rule given only the disclosed
seed prefix must return the same attack choice on all seeds sharing it;
this mathematical information restriction does NOT imply that the
remaining PRNG outputs are uniformly distributed or cryptographically
unpredictable. The applied NOR-27 SHA256/Python Random experiment studies
the behavior of one specified toy sampler, not a general CSPRNG theorem.
-/

namespace MathCan.NOR27SeedLeakage

universe u v w

/-- A residual changed-coordinate mask is defined after the t public-risk
checks and ell disclosed random-reserve checks, all of which the
radius-r attacker has avoided. -/
def legalRemainingMask (remaining r : Nat) (mask : List Bool) : Prop :=
  mask.length = remaining ∧
    (mask.filter (fun changed => changed)).length = r

/-- The exact numerator of still-undetected continuations is counted
by selecting u-ell positions only from unchanged residual coordinates. -/
def previewMissCount (mask : List Bool) (unrevealed : Nat) : Nat :=
  (MathCan.NOR23CoordinateAudit.kSubsets
    (mask.filter (fun changed => !changed)) unrevealed).length

/-- The complete number of possible uniform continuation schedules. -/
def previewTotalCount (mask : List Bool) (unrevealed : Nat) : Nat :=
  (MathCan.NOR23CoordinateAudit.kSubsets mask unrevealed).length

/-- For an attack committed after ell random checks are revealed,
the exact finite miss/total count pair uses the residual
N=m-t-ell and residual reserve size u-ell. -/
theorem conditional_preview_exact_counts
    (mask : List Bool) (m t u r ell : Nat)
    (remaining : mask.length = m-t-ell)
    (radius : (mask.filter (fun changed => changed)).length = r) :
    (previewMissCount mask (u-ell),
     previewTotalCount mask (u-ell)) =
      (MathCan.NOR23CoordinateAudit.binomial (m-t-ell-r) (u-ell),
       MathCan.NOR23CoordinateAudit.binomial (m-t-ell) (u-ell)) := by
  have h := MathCan.NOR23CoordinateAudit.exact_hypergeometric_miss_pair
    mask (u-ell)
  simpa [previewMissCount,previewTotalCount,remaining,radius] using h

/-- Every list, including the empty one, has exactly one way
to choose an empty reserve schedule. -/
theorem zero_continuation_schedule_count {α : Type u}
    (xs : List α) :
    (MathCan.NOR23CoordinateAudit.kSubsets xs 0).length = 1 := by
  cases xs with
  | nil => rfl
  | cons _ _ => rfl

/-- Once the entire reserve has been previewed, the attacker can choose
an altered position only among unchecked coordinates. With zero
secret continuation draws there is one schedule and it misses. -/
theorem complete_preview_has_zero_additional_detection
    (mask : List Bool) :
    previewMissCount mask 0 = previewTotalCount mask 0 := by
  calc
    previewMissCount mask 0 = 1 := by
      exact zero_continuation_schedule_count
        (mask.filter (fun changed => !changed))
    _ = previewTotalCount mask 0 := by
      exact (zero_continuation_schedule_count mask).symm

/-- Two seeds that produce the same disclosed leakage value are
indistinguishable to any deterministic attacker constrained to use
only the leakage value. The audit continuation can still differ. -/
theorem same_leaked_seed_prefix_same_attack_choice
    {Seed : Type u} {Leak : Type v} {Attack : Type w}
    (leak : Seed → Leak) (attacker : Leak → Attack)
    (s₁ s₂ : Seed) (identicalPreview : leak s₁ = leak s₂) :
    attacker (leak s₁) = attacker (leak s₂) :=
  congrArg attacker identicalPreview

/-- A single leaked bit can completely reveal a pathologically
constructed sampler's probe even when the seed retains an arbitrary
private payload. Therefore seed-prefix length alone does not prove
the continuation-uniformity used in the hypergeometric count. -/
def pathologicalProbe (seed : Bool × Nat) : Bool := seed.1

theorem exposed_bit_can_determine_probe_with_hidden_seed_remaining
    (leakedBit : Bool) (hidden₁ hidden₂ : Nat) :
    pathologicalProbe (leakedBit,hidden₁) =
      pathologicalProbe (leakedBit,hidden₂) := by
  rfl

/-- An attacker that learns the full realized schedule again has a
constructive different hidden target with exactly the same authenticated
ordered witness transcript, whenever at least one coordinate remains
unchecked. -/
theorem complete_schedule_disclosure_preserves_evasion
    {Coordinate : Type u}
    (checked : List Coordinate)
    (target : Coordinate → Int)
    (unseen : ∃ i : Coordinate, i ∉ checked) :
    ∃ altered : Coordinate → Int,
      altered ≠ target ∧
      MathCan.NOR24SequentialWitness.readTranscript checked target =
        MathCan.NOR24SequentialWitness.readTranscript checked altered :=
  MathCan.NOR25UniformReserve.schedule_visible_attacker_has_identical_transcript
    checked target unseen

#print axioms conditional_preview_exact_counts
#print axioms zero_continuation_schedule_count
#print axioms complete_preview_has_zero_additional_detection
#print axioms same_leaked_seed_prefix_same_attack_choice
#print axioms exposed_bit_can_determine_probe_with_hidden_seed_remaining
#print axioms complete_schedule_disclosure_preserves_evasion

end MathCan.NOR27SeedLeakage
