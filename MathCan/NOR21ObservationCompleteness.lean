import MathCan.NOR19StreamedVerifier

/-!
# NOR-21: degree-independent exactness and the complete-family boundary

A finite exact public checker at any degree reports a set of compatible
programs. An empty accepted set calls for abstention. When the true
program belongs to that set, unanimous hypothetical query predictions
are sound; when the public data admit a valid world and a contradictory
hidden future label, no deterministic public-only selector can be
correct in both worlds.

The input-degree parameter never changes the logic of exact equality,
only the finite length of public coefficient arrays and the number of
reciprocal-series multiplication sites. We also give an exact
triangular recurrence for the number of coefficient products in a
normalized reciprocal of degree n.

These are abstract exact-soundness and arithmetic-complexity facts.
The companion NOR-21 CPython experiment separately measures degrees
512 and 1024 and regenerates hidden futures only after public choices
are frozen.
-/

namespace MathCan.NOR21ObservationCompleteness

universe u v
variable {Candidate : Type u} {Public : Type v}

/-- Pick the first publicly compatible candidate from an exact finite
    enumeration. This is intentionally a total Option-valued verifier. -/
def firstPublicMatch : List Candidate → (Candidate → Bool) → Option Candidate
  | [], _ => none
  | c :: rest, accepts =>
      if accepts c then some c else firstPublicMatch rest accepts

/-- When every enumerated program fails exact public verification, the
    total finite checker abstains. This also covers maliciously
    modified demonstrations incompatible with the candidate grammar. -/
theorem empty_public_mask_must_abstain :
    ∀ candidates : List Candidate, ∀ accepts : Candidate → Bool,
      (∀ c, c ∈ candidates → accepts c = false) →
      firstPublicMatch candidates accepts = none := by
  intro candidates
  induction candidates with
  | nil =>
      intro accepts h
      rfl
  | cons c cs ih =>
      intro accepts h
      have hc : accepts c = false := h c (by simp)
      have hrest : ∀ x, x ∈ cs → accepts x = false := by
        intro x hx
        exact h x (by simp [hx])
      simp [firstPublicMatch, hc, ih accepts hrest]

/-- A public verifier can certify a future target exactly when the
    planted true program is among the public accepted candidates
    and all accepted programs predict the same query output. -/
theorem complete_family_public_unanimity_is_sound
    {Output : Type u}
    (accepted : Candidate → Prop)
    (predict : Candidate → Output)
    (actual chosen : Candidate)
    (actualMember : accepted actual)
    (unanimous : ∀ candidate,
      accepted candidate → predict candidate = predict chosen) :
    predict actual = predict chosen := by
  exact unanimous actual actualMember

/-- Two possible worlds with identical public observation and distinct
    future outputs force any deterministic public-only *possibly
    abstaining* selector to miss at least one of their exact targets.
    An abstention is counted as incomplete for this strong pointwise
    correct-output proposition. -/
theorem identical_public_worlds_cannot_both_be_future_correct
    {Output : Type u}
    (selector : Public → Option Output)
    (observation : Public)
    (validFuture adversarialFuture : Output)
    (different : validFuture ≠ adversarialFuture) :
    selector observation ≠ some validFuture ∨
      selector observation ≠ some adversarialFuture := by
  by_cases h : selector observation = some validFuture
  · right
    intro h2
    apply different
    apply Option.some.inj
    calc
      some validFuture = selector observation := h.symm
      _ = some adversarialFuture := h2
  · exact Or.inl h

/-- If a public-only selector emits the program-family-valid future
    on a particular observation, it must emit the same output for a
    counterfactual world with the same observation and an altered
    target. The latter output is therefore wrong. -/
theorem hidden_future_override_breaks_unconditional_certification
    {Output : Type u}
    (selector : Public → Option Output)
    (observation : Public)
    (validFuture alteredFuture : Output)
    (selected : selector observation = some validFuture)
    (different : validFuture ≠ alteredFuture) :
    selector observation ≠ some alteredFuture := by
  intro h
  apply different
  apply Option.some.inj
  calc
    some validFuture = selector observation := selected.symm
    _ = some alteredFuture := h

/-- Coefficient-by-coefficient streaming exactness holds for every
    finite horizon, including 512, 1024 and all other lengths.
    No bound on coefficient magnitudes enters the theorem. -/
theorem streamed_integer_verifier_exact_at_every_degree
    (candidate publicTarget : List Int) :
    MathCan.NOR19StreamedVerifier.streamingEquals
      candidate publicTarget = true ↔ candidate = publicTarget := by
  exact MathCan.NOR19StreamedVerifier.streamed_exactly_iff_materialized_equal
    candidate publicTarget

/-- Counting products in the normalized reciprocal recurrence:
    coefficient i adds exactly i integer products. -/
def inverseCoefficientProducts : Nat → Nat
  | 0 => 0
  | n + 1 => inverseCoefficientProducts n + (n+1)

/-- The exact recurrence product count is triangular at every degree. -/
theorem reciprocal_product_count_exact (n : Nat) :
    2 * inverseCoefficientProducts n = n*(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 2*(inverseCoefficientProducts n+(n+1)) =
        (n+1)*(n+2)
      calc
        2*(inverseCoefficientProducts n+(n+1)) =
          2*inverseCoefficientProducts n+2*(n+1) := by
            exact Nat.mul_add 2 (inverseCoefficientProducts n) (n+1)
        _ = n*(n+1)+2*(n+1) := by rw [ih]
        _ = (n+2)*(n+1) := by
          rw [← Nat.add_mul]
        _ = (n+1)*(n+2) := by ac_rfl

/-- Incrementing the degree by one adds exactly n+1 recurrence products. -/
theorem reciprocal_product_increment (n : Nat) :
    inverseCoefficientProducts (n+1) =
      inverseCoefficientProducts n+(n+1) := rfl

/-- Streaming eliminates thirty-two candidate-output coefficient arrays
    in the abstract NOR-19 workspace model at *any* degree. -/
theorem streamed_saves_thirty_two_outputs_at_scaled_degree
    (degree : Nat) :
    MathCan.NOR19StreamedVerifier.publicWorkspaceSlots
      (degree+1) 4 32 =
    MathCan.NOR19StreamedVerifier.publicWorkspaceSlots
      (degree+1) 4 0 + 32*(degree+1) := by
  exact MathCan.NOR19StreamedVerifier.streamed_saves_thirty_two_materialized_outputs
    (degree+1)

#print axioms empty_public_mask_must_abstain
#print axioms complete_family_public_unanimity_is_sound
#print axioms identical_public_worlds_cannot_both_be_future_correct
#print axioms hidden_future_override_breaks_unconditional_certification
#print axioms streamed_integer_verifier_exact_at_every_degree
#print axioms reciprocal_product_count_exact
#print axioms reciprocal_product_increment
#print axioms streamed_saves_thirty_two_outputs_at_scaled_degree

end MathCan.NOR21ObservationCompleteness
