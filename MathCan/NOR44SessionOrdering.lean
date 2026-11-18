import MathCan.NOR43AuthenticatedRoot

/-!
NOR-44: conditional signed session/precommit/challenge soundness.

The operational NOR44 Python harness has two separately pinned Ed25519
identities, a verifier-stored first proposal receipt, a provider-signed
source/nonce-bound Merkle root, and a verifier-selected exact challenge set.
The session's valid stage ordering is expressed here as a finite relation.

The binding of the proposal digest, authenticated root, root honesty,
Merkle opening soundness, and exact challenge ownership are *explicit*
hypotheses. This file neither proves SHA256/Ed25519 security nor derives
the external true-output provider's honesty. It establishes the logical
guarantee of those premises without a source-dependent empirical assumption.
-/

namespace MathCan.NOR44SessionOrdering

universe u v w

inductive Phase where
  | created
  | proposalCommitted
  | referenceAuthenticated
  | challengeIssued
  | finalized
  | failed
  deriving Repr, DecidableEq

/-- The only accepted state transitions of the reference session. -/
def MayAdvance : Phase → Phase → Prop
  | .created, .proposalCommitted => True
  | .proposalCommitted, .referenceAuthenticated => True
  | .referenceAuthenticated, .challengeIssued => True
  | .challengeIssued, .finalized => True
  | .created, .failed => True
  | .proposalCommitted, .failed => True
  | .referenceAuthenticated, .failed => True
  | .challengeIssued, .failed => True
  | _, _ => False

/-- Challenge publication cannot precede proposal precommitment. -/
theorem challenge_not_directly_after_created :
    ¬ MayAdvance Phase.created Phase.challengeIssued := by
  simp [MayAdvance]

/-- The verifier cannot accept an authenticated root before the first
    proposal receipt is fixed. -/
theorem reference_not_directly_after_created :
    ¬ MayAdvance Phase.created Phase.referenceAuthenticated := by
  simp [MayAdvance]

/-- Once finalized, the verifier cannot issue another challenge for the
    same session and adaptively choose new read coordinates. -/
theorem finalized_session_has_no_challenge_retry :
    ¬ MayAdvance Phase.finalized Phase.challengeIssued := by
  simp [MayAdvance]

/-- Once failed, the one-use reference verifier cannot retry a challenge. -/
theorem failed_session_has_no_challenge_retry :
    ¬ MayAdvance Phase.failed Phase.challengeIssued := by
  simp [MayAdvance]

/-- With an externally binding source/session-specific proposal digest,
    the original signed precommit receipt admits at most one exact revealed
    output vector. The signature's authenticity and digest binding are
    premises, not results of this theorem. -/
theorem bound_signed_precommit_has_unique_reveal
    {m : Nat} {Ctx : Type u} {Digest : Type v}
    (commit : Ctx → (Fin m → Int) → Digest)
    (ctx : Ctx)
    (original revealed : Fin m → Int)
    (receiptDigest : Digest)
    (originalPrecommitted : commit ctx original = receiptDigest)
    (revealMatchesReceipt : commit ctx revealed = receiptDigest)
    (binding : ∀ candidate, commit ctx candidate = commit ctx original →
      candidate = original) :
    revealed = original := by
  apply binding revealed
  calc
    commit ctx revealed = receiptDigest := revealMatchesReceipt
    _ = commit ctx original := originalPrecommitted.symm

/-- Requiring returned openings to cover the verifier-owned *exact*
    requested set preserves the true discrepancy event. A collection of
    separately valid openings at easy, unrequested indices is insufficient. -/
theorem exact_challenge_set_preserves_rejection
    {m : Nat}
    (returned requested : Fin m → Prop)
    (proposal trueOutput : Fin m → Int)
    (sameIndices : ∀ i, returned i ↔ requested i) :
    NOR43AuthenticatedRoot.rejectsOn returned proposal trueOutput ↔
      NOR43AuthenticatedRoot.rejectsOn requested proposal trueOutput := by
  constructor
  · rintro ⟨i, returnedHere, differs⟩
    exact ⟨i, (sameIndices i).mp returnedHere, differs⟩
  · rintro ⟨i, requestedHere, differs⟩
    exact ⟨i, (sameIndices i).mpr requestedHere, differs⟩

/-- Full conditional NOR44 sparse verification theorem.

If the signed precommitment uniquely binds the model's original proposal
within this source/nonce/session, all returned openings are sound against
an HONEST authorized true-output root, and the returned index set equals
the trusted verifier challenge, then the final reject decision equals
intersection of the *original proposal* discrepancy support with the
verifier's requested coordinates.

Signature authenticity, proposal binding, root binding, honest provider,
opening soundness and challenge ownership are deliberately assumptions. -/
theorem authenticated_session_rejects_iff_original_true_support_hit
    {m : Nat} {Ctx : Type u} {Digest : Type v} {Root : Type w}
    (commit : Ctx → (Fin m → Int) → Digest)
    (ctx : Ctx)
    (original revealed trueFuture opened : Fin m → Int)
    (receiptDigest : Digest)
    (originalPrecommitted : commit ctx original = receiptDigest)
    (revealMatchesReceipt : commit ctx revealed = receiptDigest)
    (precommitBinding : ∀ candidate,
      commit ctx candidate = commit ctx original → candidate = original)
    (rootDigest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (authorizedRoot : Root)
    (returnedIndices requestedIndices : Fin m → Prop)
    (honestAuthorizedRoot : authorizedRoot = rootDigest trueFuture)
    (referenceBinding : NOR43AuthenticatedRoot.BindingForTrue
      rootDigest trueFuture)
    (openingSound : NOR43AuthenticatedRoot.OpeningSound
      rootDigest validOpening)
    (allReturnedOpeningsVerified :
      ∀ i, returnedIndices i → validOpening authorizedRoot i (opened i))
    (exactRequestedIndices :
      ∀ i, returnedIndices i ↔ requestedIndices i) :
    NOR43AuthenticatedRoot.rejectsOn returnedIndices revealed opened ↔
      NOR43AuthenticatedRoot.rejectsOn requestedIndices original trueFuture := by
  have sameProposal : revealed = original :=
    bound_signed_precommit_has_unique_reveal
      commit ctx original revealed receiptDigest originalPrecommitted
      revealMatchesReceipt precommitBinding
  rw [sameProposal]
  have trueAtReturned :
      NOR43AuthenticatedRoot.rejectsOn returnedIndices original opened ↔
      NOR43AuthenticatedRoot.rejectsOn returnedIndices original trueFuture :=
    NOR43AuthenticatedRoot.authenticated_sample_rejects_iff_true_support_hit
      rootDigest validOpening original trueFuture opened
      authorizedRoot returnedIndices honestAuthorizedRoot
      referenceBinding openingSound allReturnedOpeningsVerified
  exact trueAtReturned.trans
    (exact_challenge_set_preserves_rejection
      returnedIndices requestedIndices original trueFuture
      exactRequestedIndices)

#print axioms challenge_not_directly_after_created
#print axioms reference_not_directly_after_created
#print axioms finalized_session_has_no_challenge_retry
#print axioms failed_session_has_no_challenge_retry
#print axioms bound_signed_precommit_has_unique_reveal
#print axioms exact_challenge_set_preserves_rejection
#print axioms authenticated_session_rejects_iff_original_true_support_hit

end MathCan.NOR44SessionOrdering
