import MathCan.NOR45AuthorizedProgram

/-!
NOR-46: exact integer trace constraints and conditional proof of authorized
execution-root soundness.

The Python prototype supplies full transform/output arrays and checks all
coefficients. A reciprocal transform R is certified by the complete
truncated convolution identity F*R=1 in Int, with F₀=1. We prove that a strictly causal exact integer recurrence has a UNIQUE
solution. The separate equivalence between the concrete Python packed
convolution checker and the recurrence is tested in Python, not kernel-proved.

A signed program authority and an authenticated provider root are EXTERNAL
premises. The program authority might authorize a semantically wrong
program. The full-trace certificate is transparent, non-succinct, and not
zero-knowledge. This file does not prove SHA-256 or Ed25519 security.
-/

namespace MathCan.NOR46ExactIntegerTrace

/-- A strictly causal exact-integer coefficient recurrence depends only on
    coefficients of its output at indices ≤ n when generating n+1. -/
def CausalIntegerStep
    (source : Nat → Int)
    (update : (Nat → Int) → Nat → Int) : Prop :=
  source 0 = 1 ∧
    ∀ left right n,
      (∀ k, k ≤ n → left k = right k) →
      update left n = update right n

/-- Any normalized source, fixed initial coefficient and deterministic
    strictly causal EXACT integer recurrence determine a UNIQUE infinite
    output sequence. The concrete Python convolution proof checker must
    separately establish that its all-prefix arithmetic identities imply
    this recurrence. No finite-field arithmetic or overflow is assumed. -/
theorem unique_normalized_inverse_from_causal_integer_recurrence
    (source left right : Nat → Int)
    (update : (Nat → Int) → Nat → Int)
    (stepCausal : CausalIntegerStep source update)
    (leftZero : left 0 = 1)
    (rightZero : right 0 = 1)
    (leftStep : ∀ n, left (n + 1) = update left n)
    (rightStep : ∀ n, right (n + 1) = update right n) :
    left = right := by
  have hprefix : ∀ n, ∀ k, k ≤ n → left k = right k := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have h0 : k = 0 := by omega
      rw [h0, leftZero, rightZero]
    | succ n ih =>
      intro k hk
      by_cases hsmall : k ≤ n
      · exact ih k hsmall
      · have hnext : k = n + 1 := by omega
        rw [hnext, leftStep, rightStep]
        exact stepCausal.2 left right n ih
  funext n
  exact hprefix n n (Nat.le_refl n)

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

#print axioms unique_normalized_inverse_from_causal_integer_recurrence
#print axioms verified_trace_root_is_authorized_execution_root
#print axioms verified_trace_opening_matches_authorized_program
#print axioms source_bound_trace_sparse_rejection_equivalence

end MathCan.NOR46ExactIntegerTrace
