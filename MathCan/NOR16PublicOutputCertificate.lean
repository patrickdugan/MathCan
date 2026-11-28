import Init

/-!
# NOR-16S: complete-public-observation certificates and selective abstention

A verifier checks every program in a finite candidate family against all
available public demonstrations, then simulates the publicly accepted
programs on the known QUERY INPUT. The query OUTPUT remains withheld.

If every publicly compatible program predicts the same output y, then y
is necessarily correct for an actual generator drawn from that family.
If two compatible programs predict different outputs, no such exact
public-output certificate can be issued.

These are logical statements conditional on membership of the true
generator in the candidate family and exact public candidate semantics.
The associated NOR-16 empirical result found 52 such certified public
sources among 192 test cases, with 140 counterfactual ambiguity pairs.
-/

namespace MathCan.NOR16PublicOutputCertificate

universe u v

/-- A public certificate asserts that every compatible candidate
    program yields the proposed future query output. -/
def CompleteOutputCertificate
    {Program : Type u} {Output : Type v}
    (publiclyAccepted : Program → Prop)
    (queryPrediction : Program → Output)
    (proposed : Output) : Prop :=
  ∀ program, publiclyAccepted program →
    queryPrediction program = proposed

/-- Conditional soundness: if the planted true program is among the
    publicly accepted candidates, complete predictive unanimity
    guarantees its future output matches the proposed answer. -/
theorem sound_complete_public_output_certificate
    {Program : Type u} {Output : Type v}
    (publiclyAccepted : Program → Prop)
    (queryPrediction : Program → Output)
    (planted : Program) (proposed : Output)
    (trueProgramIsAccepted : publiclyAccepted planted)
    (certificate :
      CompleteOutputCertificate publiclyAccepted queryPrediction proposed) :
    queryPrediction planted = proposed := by
  exact certificate planted trueProgramIsAccepted

/-- In particular, a unique accepted candidate determines the
    generating program's output, whenever the generator belongs to the
    enumerated candidate family. -/
theorem unique_accepted_candidate_certifies_future
    {Program : Type u} {Output : Type v}
    (publiclyAccepted : Program → Prop)
    (queryPrediction : Program → Output)
    (planted unique : Program)
    (trueProgramIsAccepted : publiclyAccepted planted)
    (uniqueAccepted :
      ∀ p, publiclyAccepted p → p = unique) :
    queryPrediction planted = queryPrediction unique := by
  have h : planted = unique :=
    uniqueAccepted planted trueProgramIsAccepted
  exact congrArg queryPrediction h

/-- A public ambiguity witness consisting of two accepted programs
    predicting different outputs rules out a universally sound exact
    future-output certificate based on those public observations alone. -/
theorem incompatible_public_predictions_forbid_certificate
    {Program : Type u} {Output : Type v}
    (publiclyAccepted : Program → Prop)
    (queryPrediction : Program → Output)
    (first second : Program)
    (firstAccepted : publiclyAccepted first)
    (secondAccepted : publiclyAccepted second)
    (differentFuture :
      queryPrediction first ≠ queryPrediction second) :
    ∀ proposed, ¬ CompleteOutputCertificate publiclyAccepted
                  queryPrediction proposed := by
  intro proposed cert
  apply differentFuture
  calc
    queryPrediction first = proposed := cert first firstAccepted
    _ = queryPrediction second := (cert second secondAccepted).symm

/-- If the true generator is publicly accepted and every compatible
    program predicts the proposed output, rejecting that output would
    be a false negative within the declared candidate family. -/
theorem accepted_program_unanimity_is_complete
    {Program : Type u} {Output : Type v}
    (publiclyAccepted : Program → Prop)
    (queryPrediction : Program → Output)
    (planted : Program) (proposed : Output)
    (membership : publiclyAccepted planted)
    (unanimous : ∀ p, publiclyAccepted p →
                   queryPrediction p = proposed) :
    queryPrediction planted = proposed := by
  exact unanimous planted membership

#print axioms sound_complete_public_output_certificate
#print axioms unique_accepted_candidate_certifies_future
#print axioms incompatible_public_predictions_forbid_certificate
#print axioms accepted_program_unanimity_is_complete

end MathCan.NOR16PublicOutputCertificate
