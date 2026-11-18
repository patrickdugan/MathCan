import MathCan.NOR45AuthorizedProgram

/-!
NOR-46: exact integer trace constraints and conditional proof of authorized
execution-root soundness.

The Python prototype supplies full transform/output arrays and checks all
coefficients. A reciprocal transform R is certified by the complete
truncated convolution identity F*R=1 in Int, with F₀=1. We prove that
such an inverse witness is UNIQUE, without relying on finite-field
arithmetic or an unproved cryptographic soundness proposition.

A signed program authority and an authenticated provider root are EXTERNAL
premises. The program authority might authorize a semantically wrong
program. The full-trace certificate is transparent, non-succinct, and not
zero-knowledge. This file does not prove SHA-256 or Ed25519 security.
-/

namespace MathCan.NOR46ExactIntegerTrace

/-- Exact truncated convolution over integral coefficients. -/
def prefixConvolution (source candidate : Nat → Int) (n : Nat) : Int :=
  (Finset.range (n + 1)).sum fun k => source (n - k) * candidate k

/-- Normalized series admit at most one exact integer right-inverse
    through EVERY finite prefix coefficient. The result uses whole
    integer identities, avoiding any finite-field wraparound premise. -/
theorem unique_normalized_inverse_from_all_prefixes
    (source left right : Nat → Int)
    (sourceUnit : source 0 = 1)
    (leftInverse : ∀ n, prefixConvolution source left n =
      if n = 0 then 1 else 0)
    (rightInverse : ∀ n, prefixConvolution source right n =
      if n = 0 then 1 else 0) :
    left = right := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hprefix :
        (Finset.range n).sum (fun k => source (n - k) * left k) =
        (Finset.range n).sum (fun k => source (n - k) * right k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k (Finset.mem_range.mp hk)]
    have hl := leftInverse n
    have hr := rightInverse n
    dsimp [prefixConvolution] at hl hr
    rw [Finset.sum_range_succ] at hl hr
    have hzero : source (n - n) = 1 := by
      simpa using sourceUnit
    rw [hzero, one_mul] at hl hr
    rw [hprefix] at hl
    omega

/-- If a FULL exact-integer trace satisfies a fixed authorized
    program's deterministic execution relation, a signed root committing
    to the trace commits to that program's output. This is a conditional
    logic theorem, not proof that the trace-verifier implementation or
    signature/hash primitives are secure. -/
theorem verified_trace_root_is_authorized_execution_root
    {m : Nat} {Prog Input Root : Type}
    (execute : Prog → Input → (Fin m → Int))
    (digest : (Fin m → Int) → Root)
    (authorizedProgram : Prog) (source : Input)
    (fullVerifiedTrace : Fin m → Int)
    (authorizedProviderRoot : Root)
    (allExactIntegerConstraints :
      fullVerifiedTrace = execute authorizedProgram source)
    (signedRootMatchesTrace :
      authorizedProviderRoot = digest fullVerifiedTrace) :
    authorizedProviderRoot = digest (execute authorizedProgram source) := by
  simpa [allExactIntegerConstraints] using signedRootMatchesTrace

/-- Binding a FULL exact trace to the original signed reference root
    preserves NOR45's conditional sparse-opening correctness theorem
    for the independently authorized program's output. -/
theorem verified_trace_opening_matches_authorized_program
    {m : Nat} {Prog Input Root : Type}
    (execute : Prog → Input → (Fin m → Int))
    (digest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (program : Prog) (source : Input)
    (traceOutput : Fin m → Int)
    (providerRoot : Root)
    (traceExact : traceOutput = execute program source)
    (rootMatchesTrace : providerRoot = digest traceOutput)
    (binding : NOR43AuthenticatedRoot.BindingForTrue
      digest (execute program source))
    (openingSound : NOR43AuthenticatedRoot.OpeningSound
      digest validOpening)
    (index : Fin m) (openedValue : Int)
    (proofValid : validOpening providerRoot index openedValue) :
    openedValue = execute program source index := by
  have hroot : providerRoot = digest (execute program source) :=
    verified_trace_root_is_authorized_execution_root
      execute digest program source traceOutput providerRoot
      traceExact rootMatchesTrace
  exact NOR45AuthorizedProgram.verified_opening_matches_authorized_program
    execute digest validOpening program program source rfl
    providerRoot hroot binding openingSound index openedValue proofValid

/-- Signed proposal commitment, program root and requested read indices
    can be composed after full exact trace verification, with every
    cryptographic binding still stated as a premise. -/
theorem source_bound_trace_sparse_rejection_equivalence
    {m : Nat} {Ctx Digest Prog Input Root : Type}
    (commit : Ctx → (Fin m → Int) → Digest)
    (ctx : Ctx)
    (original revealed opened : Fin m → Int)
    (firstDigest : Digest)
    (firstReceipt : commit ctx original = firstDigest)
    (revealMatchesReceipt : commit ctx revealed = firstDigest)
    (proposalBinding : ∀ candidate,
      commit ctx candidate = commit ctx original → candidate = original)
    (execute : Prog → Input → (Fin m → Int))
    (program : Prog) (source : Input)
    (rootDigest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (traceOutput : Fin m → Int)
    (providerRoot : Root)
    (traceExact : traceOutput = execute program source)
    (rootMatchesTrace : providerRoot = rootDigest traceOutput)
    (rootBinding : NOR43AuthenticatedRoot.BindingForTrue
      rootDigest (execute program source))
    (openingSound : NOR43AuthenticatedRoot.OpeningSound
      rootDigest validOpening)
    (returned requested : Fin m → Prop)
    (returnedOpeningsValid : ∀ i, returned i →
      validOpening providerRoot i (opened i))
    (exactVerifierIndices : ∀ i, returned i ↔ requested i) :
    NOR43AuthenticatedRoot.rejectsOn returned revealed opened ↔
      NOR43AuthenticatedRoot.rejectsOn requested original
        (execute program source) := by
  have rootExact : providerRoot = rootDigest (execute program source) :=
    verified_trace_root_is_authorized_execution_root
      execute rootDigest program source traceOutput providerRoot
      traceExact rootMatchesTrace
  exact NOR45AuthorizedProgram.signed_precommit_and_program_root_reject_exact_authorized_support
    commit ctx original revealed opened firstDigest firstReceipt
    revealMatchesReceipt proposalBinding execute program source
    rootDigest validOpening providerRoot rootExact rootBinding
    openingSound returned requested returnedOpeningsValid
    exactVerifierIndices

#print axioms unique_normalized_inverse_from_all_prefixes
#print axioms verified_trace_root_is_authorized_execution_root
#print axioms verified_trace_opening_matches_authorized_program
#print axioms source_bound_trace_sparse_rejection_equivalence

end MathCan.NOR46ExactIntegerTrace
