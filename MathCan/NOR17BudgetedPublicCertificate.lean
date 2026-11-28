import Init

/-!
# NOR-17: prefix exclusion and budgeted complete-future certificates

A sound partial public verification filters out a candidate only when
an observable prefix disagrees. Full public rejections may eliminate
additional candidates. If an accepted candidate has a hypothetical
query output shared by every remaining possible candidate, the output
of the planted compatible program is certified.

This result is independent of a numerical verifier-check budget: 4, 8,
and 16 full candidate checks can have different coverage while sharing
the same conditional logical soundness. The precise assumptions are
(i) candidate-family membership for the planted program, (ii) sound
public-prefix rejection, (iii) sound full rejection, and (iv) exact
candidate query-output semantics. The original RRC25 empirical runner
enforces those assumptions on its synthetic finite-series generator.

The Lean kernel proves the abstract soundness and counterexample
obstruction. It does not verify the C/Python implementation, test
sample membership, or any empirical coverage statistics.
-/

namespace MathCan.NOR17BudgetedPublicCertificate

universe u v w
variable {Program : Type u} {Output : Type v}

/-- Exact public sequence equality implies equality of every prefix. -/
theorem exact_public_sequence_agreement_implies_prefix
    {Symbol : Type w}
    (fullCandidate fullObserved : List Symbol) (n : Nat)
    (h : fullCandidate = fullObserved) :
    fullCandidate.take n = fullObserved.take n := by
  exact congrArg (fun s : List Symbol => s.take n) h

/-- An accepted planted program survives a prefix filter whenever
    every fully accepted program passes the sound prefix check. -/
theorem true_program_survives_public_prefix_filter
    (fullAccepted prefixAccepted : Program → Prop)
    (planted : Program)
    (prefixSound : ∀ p, fullAccepted p → prefixAccepted p)
    (trueAccepted : fullAccepted planted) :
    prefixAccepted planted := by
  exact prefixSound planted trueAccepted

/-- A true compatible generator cannot be discarded by a sound
    full public rejection. -/
theorem true_program_survives_full_rejections
    (fullAccepted rejected : Program → Prop)
    (planted : Program)
    (rejectionSound : ∀ p, rejected p → ¬ fullAccepted p)
    (trueAccepted : fullAccepted planted) :
    ¬ rejected planted := by
  intro hRejected
  exact (rejectionSound planted hRejected) trueAccepted

/-- Proof rule for a finite candidate family after partial screening
    and bounded exact checks.

    The chosen program must pass full verification. All candidates
    not soundly eliminated by prefix or full checks must predict the
    same query output as chosen. The planted true program therefore
    predicts that output too. -/
theorem sound_budgeted_public_output_certificate
    (fullAccepted prefixAccepted rejected : Program → Prop)
    (queryPrediction : Program → Output)
    (planted chosen : Program)
    (trueAccepted : fullAccepted planted)
    (chosenAccepted : fullAccepted chosen)
    (prefixSound : ∀ p, fullAccepted p → prefixAccepted p)
    (rejectionSound : ∀ p, rejected p → ¬ fullAccepted p)
    (unanimity : ∀ p, prefixAccepted p → ¬ rejected p →
       queryPrediction p = queryPrediction chosen) :
    fullAccepted chosen ∧
      queryPrediction planted = queryPrediction chosen := by
  constructor
  · exact chosenAccepted
  · have hPrefix := prefixSound planted trueAccepted
    have hNotRejected : ¬ rejected planted :=
      true_program_survives_full_rejections
        fullAccepted rejected planted rejectionSound trueAccepted
    exact unanimity planted hPrefix hNotRejected

/-- Once candidate exclusion is sound, eliminating more candidates
    preserves any existing common predicted-output certificate. This
    expresses the logical monotonicity behind incremental verification;
    physical policy coverage also depends on which witnesses are checked. -/
theorem unanimous_prediction_survives_sound_refinement
    (remainingOld remainingNew : Program → Prop)
    (queryPrediction : Program → Output)
    (output : Output)
    (newSubsetOld : ∀ p, remainingNew p → remainingOld p)
    (unanimousOld : ∀ p, remainingOld p →
      queryPrediction p = output) :
    ∀ p, remainingNew p → queryPrediction p = output := by
  intro p hNew
  exact unanimousOld p (newSubsetOld p hNew)

/-- If two accepted programs survive sound screening and imply
    different query outputs, no output can be unanimously justified
    by the remaining public candidate set. -/
theorem incompatible_surviving_predictions_forbid_certificate
    (remaining : Program → Prop)
    (queryPrediction : Program → Output)
    (a b : Program)
    (ha : remaining a)
    (hb : remaining b)
    (hDifferent : queryPrediction a ≠ queryPrediction b) :
    ¬ ∃ y : Output, ∀ p, remaining p → queryPrediction p = y := by
  intro h
  rcases h with ⟨y,hUnanimous⟩
  apply hDifferent
  calc
    queryPrediction a = y := hUnanimous a ha
    _ = queryPrediction b := (hUnanimous b hb).symm

/-- An explicit abstention premise can be introduced by a classifier
    when no unanimously supported candidate future exists. That
    abstention is consistent with a sound-certificate-only policy. -/
theorem ambiguity_requires_abstention_for_complete_certificates
    (remaining : Program → Prop)
    (queryPrediction : Program → Output)
    (a b : Program)
    (ha : remaining a) (hb : remaining b)
    (hDifferent : queryPrediction a ≠ queryPrediction b) :
    ∀ y, ¬ (∀ p, remaining p → queryPrediction p = y) := by
  intro y h
  exact incompatible_surviving_predictions_forbid_certificate
    remaining queryPrediction a b ha hb hDifferent ⟨y,h⟩

#print axioms exact_public_sequence_agreement_implies_prefix
#print axioms true_program_survives_public_prefix_filter
#print axioms true_program_survives_full_rejections
#print axioms sound_budgeted_public_output_certificate
#print axioms unanimous_prediction_survives_sound_refinement
#print axioms incompatible_surviving_predictions_forbid_certificate
#print axioms ambiguity_requires_abstention_for_complete_certificates

end MathCan.NOR17BudgetedPublicCertificate
