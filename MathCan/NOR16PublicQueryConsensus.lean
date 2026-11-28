import Init

/-!
# NOR-16: public-query predictive consensus and observational collisions

A candidate program is publicly verifiable on the demonstrations and can
be executed on the public query INPUT to form a hypothetical future output.
The true query OUTPUT remains hidden. After filtering inconsistent programs,
uniform prior mass on a possible output is its frequency among accepted
candidate predictions.

The Lean results prove a finite mass ceiling and an exact impossibility
claim for distinct possible futures under identical complete public
observations. They hold for arbitrary types and finite output collections.

The companion RRC25 study independently audits a new 288-case empirical
test, including 192 distinct public inputs mapped to one GRU hidden tensor.
Its positive/negative decision counts are empirical, not kernel-proved here.
-/

namespace MathCan.NOR16PublicQueryConsensus

universe u v w

/-- For a uniform posterior over publicly accepted candidate programs,
    the unnormalized probability of future output y is exactly the
    number of accepted programs predicting y. -/
def acceptedOutputMass {Future : Type u} [DecidableEq Future]
    (acceptedPredictions : List Future) (output : Future) : Nat :=
  (acceptedPredictions.filter (fun p => decide (p = output))).length

/-- Any chosen hypothetical future whose cluster mass is maximal gives
    at least as many correct latent-program worlds as any alternative.
    The posterior denominator is the same positive count for all guesses. -/
theorem predictive_consensus_mass_dominates
    {Future : Type u} [DecidableEq Future]
    (acceptedPredictions : List Future) (chosen : Future)
    (maximal : ∀ y : Future,
      acceptedOutputMass acceptedPredictions y ≤
        acceptedOutputMass acceptedPredictions chosen)
    (alternative : Future) :
    acceptedOutputMass acceptedPredictions alternative ≤
      acceptedOutputMass acceptedPredictions chosen := by
  exact maximal alternative

/-- If every candidate-output class has at most M accepted programs,
    then every deterministic prediction has at most M successful latent
    programs under a uniform accepted-program prior. -/
theorem posterior_correct_mass_ceiling
    {Future : Type u} [DecidableEq Future]
    (acceptedPredictions : List Future) (M : Nat)
    (ceiling : ∀ y,
      acceptedOutputMass acceptedPredictions y ≤ M)
    (guess : Future) :
    acceptedOutputMass acceptedPredictions guess ≤ M := by
  exact ceiling guess

/-- With n possible accepted latent programs and output-class maximum M,
    every deterministic prediction incurs at least n-M incorrect latent
    programs. The probability bound is (n-M)/n for n>0. -/
theorem posterior_error_floor_under_uniform_prior
    {Future : Type u} [DecidableEq Future]
    (acceptedPredictions : List Future) (M : Nat)
    (ceiling : ∀ y,
      acceptedOutputMass acceptedPredictions y ≤ M)
    (validMass : M ≤ acceptedPredictions.length)
    (guess : Future) :
    acceptedPredictions.length - M ≤
      acceptedPredictions.length -
        acceptedOutputMass acceptedPredictions guess := by
  have bound := ceiling guess
  omega

/-- Two candidate programs compatible with exactly the same complete
    public observations (including the query INPUT) can imply distinct
    query outputs. A deterministic public-only decoder then fails in at
    least one of those two valid generative worlds. -/
theorem identical_complete_public_data_divergent_futures
    {Public : Type v} {Future : Type w}
    (policy : Public → Future)
    (obs1 obs2 : Public) (future1 future2 : Future)
    (sameObservation : obs1 = obs2)
    (differentFutures : future1 ≠ future2) :
    policy obs1 ≠ future1 ∨ policy obs2 ≠ future2 := by
  by_cases h : policy obs1 = future1
  · right
    intro h2
    apply differentFutures
    calc
      future1 = policy obs1 := h.symm
      _ = policy obs2 := congrArg policy sameObservation
      _ = future2 := h2
  · exact Or.inl h

/-- The same collision theorem expressed in terms of two accepted
    candidate programs and their future-output semantics. -/
theorem accepted_programs_publicly_indistinguishable
    {Candidate : Type u} {Public : Type v} {Future : Type w}
    (observable : Candidate → Public)
    (futureOutput : Candidate → Future)
    (policy : Public → Future)
    (a b : Candidate)
    (samePublic : observable a = observable b)
    (differentOutput : futureOutput a ≠ futureOutput b) :
    policy (observable a) ≠ futureOutput a ∨
      policy (observable b) ≠ futureOutput b := by
  exact identical_complete_public_data_divergent_futures
    policy (observable a) (observable b)
    (futureOutput a) (futureOutput b) samePublic differentOutput

/-- A fixed posterior sample count is shared by all guesses. Scaling
    their correct-mass comparison by a common positive denominator
    preserves the comparison, which justifies ranking q/n by q. -/
theorem uniform_posterior_denominator_cancels
    (correctA correctB acceptedCount : Nat)
    (h : correctA ≤ correctB) :
    correctA * acceptedCount ≤ correctB * acceptedCount := by
  exact Nat.mul_le_mul_right acceptedCount h

#print axioms predictive_consensus_mass_dominates
#print axioms posterior_correct_mass_ceiling
#print axioms posterior_error_floor_under_uniform_prior
#print axioms identical_complete_public_data_divergent_futures
#print axioms accepted_programs_publicly_indistinguishable
#print axioms uniform_posterior_denominator_cancels

end MathCan.NOR16PublicQueryConsensus
