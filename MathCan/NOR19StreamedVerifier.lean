import Init

/-!
# NOR-19: exact streamed equality with a bounded candidate buffer

An exact verification predicate can compare each public coefficient
sequentially, rejecting on the first mismatch and returning success
after all coefficients match. The result is equivalent to materializing
the candidate output and comparing the full finite lists.

The RRC25 cached demonstration verifier needs four shared unary
transforms. Eager caching can retain up to 32 full candidate-output
vectors across two demonstrations, whereas a sequential checker
materializes no full candidate-output vector, and a four-class chunk
checker materializes no more than four. A simple coefficient-slot
workspace model gives the associated worst-case array count algebra.
It deliberately excludes big-integer byte sizes, public query buffers,
Python object overhead and garbage-collection allocator effects.

Actual memory and runtime claims require the companion NOR-19 CPython
benchmark, independently audited on previously unbenchmarked sources.
-/

namespace MathCan.NOR19StreamedVerifier

universe u

/-- Coefficient-by-coefficient equality, with finite short-circuiting.
    The final case requires equal list lengths. -/
def streamingEquals {Alpha : Type u} [DecidableEq Alpha] :
    List Alpha → List Alpha → Bool
  | [], [] => true
  | x :: xs, y :: ys =>
      decide (x = y) && streamingEquals xs ys
  | _, _ => false

/-- Sequential exact comparison agrees with whole-vector equality. -/
theorem streamed_exactly_iff_materialized_equal
    {Alpha : Type u} [DecidableEq Alpha]
    (a b : List Alpha) :
    streamingEquals a b = true ↔ a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil =>
          simp [streamingEquals]
      | cons y ys =>
          simp [streamingEquals]
  | cons x xs ih =>
      cases b with
      | nil =>
          simp [streamingEquals]
      | cons y ys =>
          simp [streamingEquals, ih]

/-- Any mismatched public coefficient (or unequal list length)
    ensures streaming rejects exactly where full equality rejects. -/
theorem streamed_rejection_iff_unequal
    {Alpha : Type u} [DecidableEq Alpha]
    (a b : List Alpha) :
    streamingEquals a b = false ↔ a ≠ b := by
  constructor
  · intro h heq
    have proof : streamingEquals a b = true :=
      (streamed_exactly_iff_materialized_equal a b).2 heq
    rw [proof] at h
    cases h
  · intro h
    cases htest : streamingEquals a b with
    | false =>
        rfl
    | true =>
        have heq := (streamed_exactly_iff_materialized_equal a b).1 htest
        exact False.elim (h heq)

/-- Exact acceptance across two public demonstrations agrees with
    streaming verification of those demonstrations in sequence. -/
theorem streamed_two_demo_acceptance_exact
    {Alpha : Type u} [DecidableEq Alpha]
    (candidate1 observed1 candidate2 observed2 : List Alpha) :
    (streamingEquals candidate1 observed1 = true ∧
      streamingEquals candidate2 observed2 = true) ↔
      (candidate1 = observed1 ∧ candidate2 = observed2) := by
  constructor
  · intro ⟨h1,h2⟩
    exact ⟨(streamed_exactly_iff_materialized_equal _ _).1 h1,
           (streamed_exactly_iff_materialized_equal _ _).1 h2⟩
  · intro ⟨h1,h2⟩
    exact ⟨(streamed_exactly_iff_materialized_equal _ _).2 h1,
           (streamed_exactly_iff_materialized_equal _ _).2 h2⟩

/-- Abstract coefficient-slot model, including the four shared
    public unary buffers for the active demonstration. -/
def publicWorkspaceSlots
    (coefficientCount unaryBuffers candidateOutputBuffers : Nat) : Nat :=
  unaryBuffers * coefficientCount +
    candidateOutputBuffers * coefficientCount

/-- Streaming requires no materialized candidate output buffers beyond
    four shared unary transformations in this abstract workspace model. -/
theorem streamed_zero_candidate_output_workspace (n : Nat) :
    publicWorkspaceSlots n 4 0 = 4*n := by
  simp [publicWorkspaceSlots]

/-- An eager two-demonstration sixteen-class cache can retain 32 full
    candidate-output arrays; streaming eliminates these 32 arrays from
    its abstract coefficient-slot workspace budget. -/
theorem streamed_saves_thirty_two_materialized_outputs (n : Nat) :
    publicWorkspaceSlots n 4 32 =
      publicWorkspaceSlots n 4 0 + 32*n := by
  simp [publicWorkspaceSlots]

/-- Four-at-a-time chunking retains at most four full output buffers,
    saving the other 28 relative to eager two-demo caching. -/
theorem four_chunk_saves_twenty_eight_outputs (n : Nat) :
    publicWorkspaceSlots n 4 32 =
      publicWorkspaceSlots n 4 4 + 28*n := by
  simp [publicWorkspaceSlots]
  omega

/-- For any nonempty finite public series, the abstract streamed
    workspace is strictly below the four-output chunked workspace. -/
theorem streamed_strictly_fewer_materialized_slots
    (n : Nat) (hPositive : 0 < n) :
    publicWorkspaceSlots n 4 0 <
      publicWorkspaceSlots n 4 4 := by
  simp [publicWorkspaceSlots]
  omega

/-- Certification remains logically conditional on every still viable
    public-compatible candidate predicting the same hypothetical future,
    independent of how verification implements vector equality. -/
theorem streamed_checker_unanimous_output_sound
    {Candidate : Type u}
    (trueCompatible stillViable : Candidate → Prop)
    (futurePrediction : Candidate → Nat)
    (planted chosen : Candidate)
    (plantedCompatible : trueCompatible planted)
    (soundSurvival : ∀ c, trueCompatible c → stillViable c)
    (unanimous : ∀ c, stillViable c →
       futurePrediction c = futurePrediction chosen) :
    futurePrediction planted = futurePrediction chosen := by
  exact unanimous planted (soundSurvival planted plantedCompatible)

#print axioms streamed_exactly_iff_materialized_equal
#print axioms streamed_rejection_iff_unequal
#print axioms streamed_two_demo_acceptance_exact
#print axioms streamed_zero_candidate_output_workspace
#print axioms streamed_saves_thirty_two_materialized_outputs
#print axioms four_chunk_saves_twenty_eight_outputs
#print axioms streamed_strictly_fewer_materialized_slots
#print axioms streamed_checker_unanimous_output_sound

end MathCan.NOR19StreamedVerifier
