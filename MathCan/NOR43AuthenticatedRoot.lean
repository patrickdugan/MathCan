import MathCan.NOR42HiddenSuffix

/-!
NOR-43: conditional soundness of authenticated sparse coefficient openings.

The operational reference verifier pins an authorized Ed25519 public key,
authenticates a signed source-bound manifest and a Merkle root, and checks a
coefficient opening at each independently chosen index. Those cryptographic
facts are assumptions here, NOT theorem conclusions: unforgeable authorized
signatures, collision/second-preimage resistance, and an HONEST external
reference provider are all outside the Lean model.

This file proves the exact logical consequence of those explicit premises.
If the pinned authorized root commits to the actual true future, each verified
opening equals the corresponding true coefficient; therefore a rejection at
any selected coordinate is equivalent to a discrepancy against true output.

A model's own commitment to its proposed vector can support internally valid
openings for a wrong vector, illustrating why Merkle self-consistency does not
provide ground-truth authentication by itself.
-/

namespace MathCan.NOR43AuthenticatedRoot

universe u

/-- An exact k-coordinate discrepancy event, parameterized by a publicly
    unknown true future and an independently selected set of read indices. -/
def rejectsOn {m : Nat} (checked : Fin m → Prop)
    (proposal reference : Fin m → Int) : Prop :=
  ∃ i, checked i ∧ proposal i ≠ reference i

/-- Binding is an explicit cryptographic premise: under the authorized root
    equality, no vector different from the true future may hash to it. -/
def BindingForTrue {m : Nat} {Root : Type u}
    (digest : (Fin m → Int) → Root)
    (trueFuture : Fin m → Int) : Prop :=
  ∀ candidate, digest candidate = digest trueFuture → candidate = trueFuture

/-- A verified opening is sound relative to *some* vector committing to the
    root. Computational Merkle binding is assumed, rather than derived. -/
def OpeningSound {m : Nat} {Root : Type u}
    (digest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop) : Prop :=
  ∀ root i value, validOpening root i value →
    ∃ candidate, digest candidate = root ∧ candidate i = value

/-- With an honestly authorized target commitment and a binding hash,
    a verified opening equals the corresponding true coefficient. -/
theorem authenticated_opening_matches_true
    {m : Nat} {Root : Type u}
    (digest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (trueFuture : Fin m → Int)
    (authorizedRoot : Root)
    (index : Fin m) (openedCoefficient : Int)
    (rootHonest : authorizedRoot = digest trueFuture)
    (binding : BindingForTrue digest trueFuture)
    (soundness : OpeningSound digest validOpening)
    (verified : validOpening authorizedRoot index openedCoefficient) :
    openedCoefficient = trueFuture index := by
  obtain ⟨candidate, hashEqual, valueEqual⟩ :=
    soundness authorizedRoot index openedCoefficient verified
  have sameHash : digest candidate = digest trueFuture := by
    calc
      digest candidate = authorizedRoot := hashEqual
      _ = digest trueFuture := rootHonest
  have sameVector : candidate = trueFuture :=
    binding candidate sameHash
  calc
    openedCoefficient = candidate index := valueEqual.symm
    _ = trueFuture index := by rw [sameVector]

/-- All checked openings are exact under the same authenticated reference
    root, without assuming anything about unchecked coefficients. -/
theorem checked_openings_match_true
    {m : Nat} {Root : Type u}
    (digest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (trueFuture opened : Fin m → Int)
    (authorizedRoot : Root)
    (checked : Fin m → Prop)
    (rootHonest : authorizedRoot = digest trueFuture)
    (binding : BindingForTrue digest trueFuture)
    (soundness : OpeningSound digest validOpening)
    (allVerified : ∀ i, checked i → validOpening authorizedRoot i (opened i)) :
    ∀ i, checked i → opened i = trueFuture i := by
  intro i hi
  exact authenticated_opening_matches_true
    digest validOpening trueFuture authorizedRoot i (opened i)
    rootHonest binding soundness (allVerified i hi)

/-- The authenticated sparse comparison rejects exactly when the proposed
    output differs from the true future at one of the checked indices.
    The verifier establishes this equivalence only under the premises. -/
theorem authenticated_sample_rejects_iff_true_support_hit
    {m : Nat} {Root : Type u}
    (digest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (proposal trueFuture opened : Fin m → Int)
    (authorizedRoot : Root)
    (checked : Fin m → Prop)
    (rootHonest : authorizedRoot = digest trueFuture)
    (binding : BindingForTrue digest trueFuture)
    (soundness : OpeningSound digest validOpening)
    (allVerified : ∀ i, checked i → validOpening authorizedRoot i (opened i)) :
    rejectsOn checked proposal opened ↔
      rejectsOn checked proposal trueFuture := by
  have accurate := checked_openings_match_true
    digest validOpening trueFuture opened authorizedRoot checked
    rootHonest binding soundness allVerified
  constructor
  · intro h
    obtain ⟨i, hi, neq⟩ := h
    refine ⟨i, hi, ?_⟩
    simpa only [accurate i hi] using neq
  · intro h
    obtain ⟨i, hi, neq⟩ := h
    refine ⟨i, hi, ?_⟩
    simpa only [accurate i hi] using neq

/-- An attacker-owned self-root may carry a locally valid Merkle opening for
    a proposed coefficient that differs from the true target. This witness
    refutes any claim that self-root inclusion alone implies truth. -/
theorem model_self_committed_opening_can_be_wrong
    {m : Nat} {Root : Type u}
    (digest : (Fin m → Int) → Root)
    (validOpening : Root → Fin m → Int → Prop)
    (proposal trueFuture : Fin m → Int)
    (index : Fin m)
    (openedIsValid : validOpening (digest proposal) index (proposal index))
    (proposalWrong : proposal index ≠ trueFuture index) :
    validOpening (digest proposal) index (proposal index) ∧
      proposal index ≠ trueFuture index := by
  exact ⟨openedIsValid, proposalWrong⟩

/-- An honest reference root is a separate premise from a valid opening
    under the model's own root. For a wrong proposal the two values differ. -/
theorem wrong_model_opening_cannot_be_opening_of_honest_reference
    {m : Nat} {Root : Type u}
    (digest : (Fin m → Int) → Root)
    (proposal trueFuture : Fin m → Int)
    (index : Fin m)
    (modelWrong : proposal index ≠ trueFuture index)
    (binding : BindingForTrue digest trueFuture) :
    digest proposal ≠ digest trueFuture := by
  intro same
  have sameVector := binding proposal same
  have sameIndex : proposal index = trueFuture index := by
    rw [sameVector]
  exact modelWrong sameIndex

#print axioms authenticated_opening_matches_true
#print axioms checked_openings_match_true
#print axioms authenticated_sample_rejects_iff_true_support_hit
#print axioms model_self_committed_opening_can_be_wrong
#print axioms wrong_model_opening_cannot_be_opening_of_honest_reference

end MathCan.NOR43AuthenticatedRoot
