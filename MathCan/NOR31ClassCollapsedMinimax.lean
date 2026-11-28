import MathCan.NOR30MixedAudit

/-!
NOR-31: quotient of duplicate audit policy classes and a template-aware
minimax feasibility constraint.

NOR-30's shuffled_prior is a uniform permutation of an arbitrary fixed
ranking. Composition with a fixed permutation is bijective on the set of
all permutations. Thus uniformly sampling permutations of that ranking
has the same exact law as directly sampling uniform permutations, and
their first k coordinate sets have the same distribution.

Whenever two auditor columns have identical payoffs in every attack
row, merging their integer weights preserves the full finite game.
A template-coverage constraint above the coverage of the uniform-only
class excludes a degenerate solution assigning zero risk-targeted mass.

The inherited mixture coverage theorem is conditional on an authentic
external target-coefficient witness and an attack fixed before
independent random audit sampling; no PRNG/cryptography claim is made.
-/

namespace MathCan.NOR31ClassCollapsedMinimax

universe u

/-- Reindex a complete proposed random ordering by a fixed coordinate
    permutation. Written in Init-only function notation so no Mathlib
    equivalence package is needed. -/
def applyFixedRanking {α : Type u}
    (ranking sampled : α → α) : α → α :=
  fun x => sampled (ranking x)

/-- Precompose with the inverse fixed coordinate ordering. -/
def undoFixedRanking {α : Type u}
    (inverseRanking sampled : α → α) : α → α :=
  fun x => sampled (inverseRanking x)

/-- A two-sided inverse for the fixed ranking explicitly undoes
    reindexing for EVERY sampled ordering. -/
theorem undo_after_apply {α : Type u}
    (ranking inverseRanking sampled : α → α)
    (hRight : ∀ x, ranking (inverseRanking x) = x) :
    undoFixedRanking inverseRanking
      (applyFixedRanking ranking sampled) = sampled := by
  funext x
  simpa [undoFixedRanking, applyFixedRanking] using
    congrArg sampled (hRight x)

theorem apply_after_undo {α : Type u}
    (ranking inverseRanking sampled : α → α)
    (hLeft : ∀ x, inverseRanking (ranking x) = x) :
    applyFixedRanking ranking
      (undoFixedRanking inverseRanking sampled) = sampled := by
  funext x
  simpa [undoFixedRanking, applyFixedRanking] using
    congrArg sampled (hLeft x)

/-- The fixed-ranking action is one-to-one and onto on all coordinate
    functions. Restricting it to finite permutations preserves uniform
    counting once closure under permutation composition is established. -/
theorem uniform_permutation_relabeling_bijective {α : Type u}
    (ranking inverseRanking : α → α)
    (left : ∀ x, inverseRanking (ranking x) = x)
    (right : ∀ x, ranking (inverseRanking x) = x) :
    (∀ a b : α → α,
      applyFixedRanking ranking a = applyFixedRanking ranking b → a = b) ∧
    (∀ target : α → α,
      ∃ source : α → α, applyFixedRanking ranking source = target) := by
  constructor
  · intro a b h
    have hh := congrArg (undoFixedRanking inverseRanking) h
    have ha := undo_after_apply ranking inverseRanking a right
    have hb := undo_after_apply ranking inverseRanking b right
    rw [ha, hb] at hh
    exact hh
  · intro target
    refine ⟨undoFixedRanking inverseRanking target, ?_⟩
    exact apply_after_undo ranking inverseRanking target left

/-- The composition of two bijective coordinate functions has an
    explicit two-sided inverse; the reindexing therefore restricts
    to the finite permutation space rather than leaving it. -/
theorem reindexing_preserves_permutations {α : Type u}
    (ranking inverseRanking sampled inverseSampled : α → α)
    (left : ∀ x, inverseRanking (ranking x) = x)
    (right : ∀ x, ranking (inverseRanking x) = x)
    (sampleLeft : ∀ x, inverseSampled (sampled x) = x)
    (sampleRight : ∀ x, sampled (inverseSampled x) = x) :
    ∃ combinedInverse : α → α,
      (∀ x, combinedInverse (applyFixedRanking ranking sampled x) = x) ∧
      (∀ x, applyFixedRanking ranking sampled (combinedInverse x) = x) := by
  refine ⟨fun x => inverseRanking (inverseSampled x), ?_, ?_⟩
  · intro x
    change inverseRanking (inverseSampled (sampled (ranking x))) = x
    rw [sampleLeft, left]
  · intro x
    change sampled (ranking (inverseRanking (inverseSampled x))) = x
    rw [right, sampleRight]

/-- Selecting a coordinate after random reindexing is the same as
    applying the random permutation to the fixed-ranked coordinate. -/
theorem permuted_ranking_sample_is_uniform_reindexing {α : Type u}
    (ranking sampled : α → α) (coordinate : α) :
    applyFixedRanking ranking sampled coordinate =
      sampled (ranking coordinate) := by
  rfl

/-- Two observationally equivalent auditor classes contribute the
    same finite-game expected numerator whether their weights are
    represented separately or merged. -/
theorem duplicate_policy_weights_collapse
    (weightUniform weightShuffled payoff otherPayoff : Nat) :
    weightUniform*payoff + weightShuffled*payoff + otherPayoff =
      (weightUniform+weightShuffled)*payoff + otherPayoff := by
  simp [Nat.add_mul]

/-- All attacker payoff rows are exactly preserved by merging a duplicate
    auditor class. The result holds for any finite roster of attacks. -/
theorem duplicate_policy_class_collapse_all_attacker_rows
    (scores : List Nat) (weightUniform weightShuffled : Nat) :
    scores.map (fun hit => weightUniform*hit + weightShuffled*hit) =
      scores.map (fun hit => (weightUniform+weightShuffled)*hit) := by
  apply List.map_congr_left
  intro x hx
  simp [Nat.add_mul]

/-- If uniform-only template coverage falls below the registered floor,
    any feasible mixture must allocate positive mass to a genuine
    nonuniform policy. Abstracts the NOR-31 empirical 18% constraint. -/
theorem template_floor_excludes_uniform_only
    (uniformWeight riskWeight uniformTemplate riskTemplate floor : Nat)
    (uniformInsufficient : uniformWeight*uniformTemplate < floor)
    (feasible : floor ≤
      uniformWeight*uniformTemplate + riskWeight*riskTemplate) :
    0 < riskWeight := by
  cases riskWeight with
  | zero =>
      have hfloor : floor ≤ uniformWeight*uniformTemplate := by
        simpa using feasible
      exact False.elim ((Nat.not_le_of_gt uniformInsufficient) hfloor)
  | succ n =>
      exact Nat.zero_lt_succ n

/-- An exact historical template lower-bound constraint remains valid
    after combining two equivalent uniform arms with equal per-arm
    coverage coefficients. -/
theorem collapsing_uniform_alias_preserves_template_numerator
    (u s uniformTemplate other : Nat) :
    u*uniformTemplate + s*uniformTemplate + other =
      (u+s)*uniformTemplate + other :=
  duplicate_policy_weights_collapse u s uniformTemplate other

/-- The nonnegative six-policy mixture inherits its exact registered
    per-arm finite lower bound from the NOR-30 generic theorem. -/
theorem constrained_mixture_inherits_blind_detection_floor
    (arms : List MathCan.NOR30MixedAudit.AuditArm)
    (sound : ∀ arm ∈ arms, arm.lower ≤ arm.observed) :
    MathCan.NOR30MixedAudit.weightedLower arms ≤
      MathCan.NOR30MixedAudit.weightedObserved arms :=
  MathCan.NOR30MixedAudit.any_mixed_policy_inherits_certified_floor arms sound

/-- An auditor with an independently sampled positive uniform component
    retains a positive blind detection floor irrespective of the other
    policy weights, provided the witness and audit-coin assumptions hold. -/
theorem reserved_uniform_weight_has_positive_floor
    (uniformWeight uniformFloor : Nat)
    (other : List MathCan.NOR30MixedAudit.AuditArm)
    (weightPos : 0 < uniformWeight)
    (floorPos : 0 < uniformFloor) :
    0 < uniformWeight*uniformFloor +
      MathCan.NOR30MixedAudit.weightedLower other :=
  MathCan.NOR30MixedAudit.positive_uniform_mass_preserves_positive_floor
    uniformWeight uniformFloor other weightPos floorPos

#print axioms undo_after_apply
#print axioms apply_after_undo
#print axioms uniform_permutation_relabeling_bijective
#print axioms reindexing_preserves_permutations
#print axioms permuted_ranking_sample_is_uniform_reindexing
#print axioms duplicate_policy_weights_collapse
#print axioms duplicate_policy_class_collapse_all_attacker_rows
#print axioms template_floor_excludes_uniform_only
#print axioms collapsing_uniform_alias_preserves_template_numerator
#print axioms constrained_mixture_inherits_blind_detection_floor
#print axioms reserved_uniform_weight_has_positive_floor

end MathCan.NOR31ClassCollapsedMinimax
