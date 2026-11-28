import MathCan.NOR44SessionOrdering

/-!
NOR-45: conditional soundness of separately authorized program execution
and a session-bound signed target-output Merkle root.

NOR-43 assumes a trusted provider has committed the actual true future.
NOR-45 uses an independently signed program, a fixed deterministic semantics,
and full independent execution to establish the intermediate property that
the signed output root commits to the exact output of THAT authorized program.

This is not proof the authorized program is real-world semantic truth. Hash
binding, Ed25519 signature authorization, program-key pinning, a correct
independent interpreter, source/query binding and verifier challenge secrecy
are hypotheses of the operational protocol. None are cryptographically
proved here. NOR-44 supplies session chronology and proposal binding.
-/

namespace MathCan.NOR45AuthorizedProgram

universe u v w t

/-- Under a separately authorized program and root of its independently
    executed coefficients, a verified sparse opening matches that program
    at this exact coordinate. "Authorized" is supplied by the caller. -/
theorem verified_opening_matches_authorized_program
    {m : Nat} {Prog : Type u} {Input : Type v} {Root : Type w}
    (execute : Prog → Input → (Fin m → Int))
    (digest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (signedProgram authorizedProgram : Prog)
    (source : Input)
    (signedProgramIsAuthorized : signedProgram = authorizedProgram)
    (providerRoot : Root)
    (providerRootMatchesExecution :
      providerRoot = digest (execute signedProgram source))
    (binding : NOR43AuthenticatedRoot.BindingForTrue digest
      (execute authorizedProgram source))
    (openingSound : NOR43AuthenticatedRoot.OpeningSound
      digest validOpening)
    (index : Fin m) (openedValue : Int)
    (proofValid : validOpening providerRoot index openedValue) :
    openedValue = execute authorizedProgram source index := by
  have rootOfAuthorized :
      providerRoot = digest (execute authorizedProgram source) := by
    simpa [signedProgramIsAuthorized] using providerRootMatchesExecution
  exact NOR43AuthenticatedRoot.authenticated_opening_matches_true
    digest validOpening (execute authorizedProgram source)
    providerRoot index openedValue rootOfAuthorized binding
    openingSound proofValid

/-- If an authorized program is executed independently and the provider's
    signed root matches its execution, the sparse decision over the exact
    requested coordinates is correct RELATIVE TO THAT PROGRAM's output. -/
theorem authorized_program_checked_rejection_equivalence
    {m : Nat} {Prog : Type u} {Input : Type v} {Root : Type w}
    (execute : Prog → Input → (Fin m → Int))
    (digest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (signedProgram authorizedProgram : Prog)
    (source : Input)
    (signedProgramIsAuthorized : signedProgram = authorizedProgram)
    (providerRoot : Root)
    (providerRootMatchesExecution :
      providerRoot = digest (execute signedProgram source))
    (binding : NOR43AuthenticatedRoot.BindingForTrue digest
      (execute authorizedProgram source))
    (openingSound : NOR43AuthenticatedRoot.OpeningSound
      digest validOpening)
    (proposal opened : Fin m → Int)
    (checked : Fin m → Prop)
    (allOpeningsVerified :
      ∀ i, checked i → validOpening providerRoot i (opened i)) :
    NOR43AuthenticatedRoot.rejectsOn checked proposal opened ↔
      NOR43AuthenticatedRoot.rejectsOn checked proposal
        (execute authorizedProgram source) := by
  have hRoot :
      providerRoot = digest (execute authorizedProgram source) := by
    simpa [signedProgramIsAuthorized] using providerRootMatchesExecution
  exact NOR43AuthenticatedRoot.authenticated_sample_rejects_iff_true_support_hit
    digest validOpening proposal (execute authorizedProgram source)
    opened providerRoot checked hRoot binding openingSound
    allOpeningsVerified

/-- If a dishonest output provider signs a different vector at even one
    coefficient, its Merkle root cannot equal the authorized program's root
    under the explicit reference-specific binding assumption. -/
theorem false_output_root_differs_from_authorized_program_root
    {m : Nat} {Prog : Type u} {Input : Type v} {Root : Type w}
    (execute : Prog → Input → (Fin m → Int))
    (digest : (Fin m → Int) → Root)
    (authorizedProgram : Prog) (source : Input)
    (providerOutput : Fin m → Int) (index : Fin m)
    (providerDisagrees :
      providerOutput index ≠ execute authorizedProgram source index)
    (binding : NOR43AuthenticatedRoot.BindingForTrue digest
      (execute authorizedProgram source)) :
    digest providerOutput ≠ digest (execute authorizedProgram source) := by
  exact NOR43AuthenticatedRoot.wrong_model_opening_cannot_be_opening_of_honest_reference
    digest providerOutput (execute authorizedProgram source)
    index providerDisagrees binding

/-- Authorized *program execution* by itself permits a false semantic
    world: an authorized program can disagree with actual true coefficients.
    Computational fidelity and semantic truth are distinct hypotheses. -/
theorem faithfully_executed_authorized_program_can_be_semantically_wrong
    {m : Nat} {Prog : Type u} {Input : Type v} {Root : Type w}
    (execute : Prog → Input → (Fin m → Int))
    (digest : (Fin m → Int) → Root)
    (authorizedProgram : Prog) (source : Input)
    (semanticTrueFuture : Fin m → Int)
    (authorizedReferenceRoot : Root) (index : Fin m)
    (executionRootCorrect :
      authorizedReferenceRoot = digest (execute authorizedProgram source))
    (programIsSemanticallyWrong :
      execute authorizedProgram source index ≠ semanticTrueFuture index) :
    authorizedReferenceRoot = digest (execute authorizedProgram source) ∧
      execute authorizedProgram source index ≠ semanticTrueFuture index := by
  exact ⟨executionRootCorrect, programIsSemanticallyWrong⟩

/-- Full session-bound conclusion, combining NOR44's first-proposal
    non-equivocation with NOR45's independently checked authorized program
    root. Exact sparse rejection then matches the ORIGINAL model proposal's
    difference support against that authorized program's execution. -/
theorem signed_precommit_and_program_root_reject_exact_authorized_support
    {m : Nat} {Ctx : Type u} {Digest : Type v}
    {Prog : Type w} {Input : Type t} {Root : Type}
    (commit : Ctx → (Fin m → Int) → Digest)
    (ctx : Ctx)
    (originalProposal revealedProposal opened : Fin m → Int)
    (firstDigest : Digest)
    (firstReceipt : commit ctx originalProposal = firstDigest)
    (revealMatchesReceipt : commit ctx revealedProposal = firstDigest)
    (proposalBinding : ∀ candidate,
      commit ctx candidate = commit ctx originalProposal →
        candidate = originalProposal)
    (execute : Prog → Input → (Fin m → Int))
    (program : Prog) (source : Input)
    (rootDigest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (providerRoot : Root)
    (rootMatchesAuthorizedExecution :
      providerRoot = rootDigest (execute program source))
    (rootBinding : NOR43AuthenticatedRoot.BindingForTrue
      rootDigest (execute program source))
    (openingSound : NOR43AuthenticatedRoot.OpeningSound
      rootDigest validOpening)
    (returned requested : Fin m → Prop)
    (returnedOpeningsValid : ∀ i, returned i →
      validOpening providerRoot i (opened i))
    (exactVerifierIndices : ∀ i, returned i ↔ requested i) :
    NOR43AuthenticatedRoot.rejectsOn returned revealedProposal opened ↔
      NOR43AuthenticatedRoot.rejectsOn requested originalProposal
        (execute program source) := by
  exact NOR44SessionOrdering.authenticated_session_rejects_iff_original_true_support_hit
    commit ctx originalProposal revealedProposal
    (execute program source) opened firstDigest firstReceipt
    revealMatchesReceipt proposalBinding rootDigest validOpening
    providerRoot returned requested rootMatchesAuthorizedExecution
    rootBinding openingSound returnedOpeningsValid exactVerifierIndices

#print axioms verified_opening_matches_authorized_program
#print axioms authorized_program_checked_rejection_equivalence
#print axioms false_output_root_differs_from_authorized_program_root
#print axioms faithfully_executed_authorized_program_can_be_semantically_wrong
#print axioms signed_precommit_and_program_root_reject_exact_authorized_support

end MathCan.NOR45AuthorizedProgram
