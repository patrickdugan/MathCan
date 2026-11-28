import MathCan.NOR21ObservationCompleteness

/-!
# NOR-22: trusted target commitments, modular collisions and information scope

NOR-21 showed that no deterministic public-only selector can be correct
on both of two worlds with identical public observations and different
hidden targets. NOR-22 introduces a *new authenticated target-dependent
signal*: a modular fingerprint of the true future, supplied by a trusted
publisher who has seen the target. This is extra information, rather than
a discovery of true target values from public demonstrations alone.

A mismatch between the predicted target's fingerprint and the publisher's
authenticated fingerprint is definitive evidence of an incorrect
prediction. Equality is only a necessary condition. The two fixed
moduli 65537 and 65521 both have explicit additive collisions; the
product-modulus shift evades both, while an untrusted candidate-created
"commitment" is always satisfied.

The experiment separately tests full polynomial evaluation at r=3, at
public query degrees 768 and 1536, with source-locked target worlds.
The algebraic theorems below concern any target representation and
the arithmetic of the modulus residues; no cryptographic security or
actual authenticated publisher is proved in Lean.
-/

namespace MathCan.NOR22ModularFutureCommitments

universe u v w
variable {Target : Type u} {Digest : Type v} {Public : Type w}

/-- Exactly matching a target's authenticated fingerprint is a
    necessary condition for the proposed target to be correct. -/
theorem authentic_fingerprint_mismatch_proves_wrong_target
    (fingerprint : Target → Digest)
    (proposed actual : Target)
    (mismatch : fingerprint proposed ≠ fingerprint actual) :
    proposed ≠ actual := by
  intro h
  exact mismatch (congrArg fingerprint h)

/-- If a fingerprint were injective on the candidate/target domain,
    an authentic equality would suffice. The injectivity assumption
    fails for the finite modular fingerprints used in NOR-22. -/
theorem authenticated_fingerprint_equal_and_injective_is_sound
    (fingerprint : Target → Digest)
    (hInjective : Function.Injective fingerprint)
    (proposed actual : Target)
    (hMatches : fingerprint proposed = fingerprint actual) :
    proposed = actual := hInjective hMatches

/-- A candidate that generates its own alleged commitment learns
    nothing about the true target: the comparison always succeeds. -/
theorem self_generated_commitment_is_vacuous
    (fingerprint : Target → Digest) (proposed : Target) :
    fingerprint proposed = fingerprint proposed := rfl

/-- If two different true futures share both the entire public source
    and an identical target signature, a deterministic selector from
    that augmented observation cannot be correct in both worlds. -/
theorem indistinguishable_public_and_commitment_worlds
    {D1 : Type v} {D2 : Type u}
    (selector : (Public × D1 × D2) → Option Target)
    (pubObservation : Public) (sig1 : D1) (sig2 : D2)
    (targetA targetB : Target)
    (hDifferent : targetA ≠ targetB) :
    selector (pubObservation,sig1,sig2) ≠ some targetA ∨
      selector (pubObservation,sig1,sig2) ≠ some targetB := by
  exact MathCan.NOR21ObservationCompleteness.identical_public_worlds_cannot_both_be_future_correct
    selector (pubObservation,sig1,sig2) targetA targetB hDifferent

/-- The concrete moduli and polynomial evaluation point registered in
    the prospective experiment. -/
def modulusP : Int := 65537
def modulusQ : Int := 65521
def evaluationPoint : Int := 3

/-- An additive change by one full p-period is invisible modulo p,
    regardless of the original target residue. -/
theorem single_modulus_period_collision (x : Int) :
    (x + modulusP) % modulusP = x % modulusP := by
  unfold modulusP
  omega

/-- An additive change by the product of both moduli leaves both
    fingerprints unchanged. It is a concrete counterexample to
    treating two short residues as an injective target encoding. -/
theorem double_modulus_product_collision (x : Int) :
    (x + modulusP * modulusQ) % modulusP = x % modulusP ∧
      (x + modulusP * modulusQ) % modulusQ = x % modulusQ := by
  unfold modulusP modulusQ
  constructor <;> omega

/-- The first modulus still catches a one-unit difference. -/
theorem unit_shift_changes_first_modulus (x : Int) :
    (x + 1) % modulusP ≠ x % modulusP := by
  unfold modulusP
  omega

/-- The second modulus detects the exact first-modulus-sized shift.
    This is the source-independent scalar modular witness behind
    the two-modulus experiment. -/
theorem p_shift_changes_second_modulus (x : Int) :
    (x + modulusP) % modulusQ ≠ x % modulusQ := by
  unfold modulusP modulusQ
  omega

/-- The p*q shift changes the actual integer even though both modular
    residues agree. -/
theorem collision_is_distinct_future (x : Int) :
    x + modulusP * modulusQ ≠ x := by
  unfold modulusP modulusQ
  omega

/-- Polynomial evaluation of a finite coefficient list at r=3.
    Degree zero appears at the head of the list, matching RRC25. -/
def polynomialAt3 : List Int → Int
  | [] => 0
  | coefficient :: rest =>
      coefficient + evaluationPoint * polynomialAt3 rest

/-- The target commitment is exactly polynomial evaluation mod p/q.
    It explicitly depends on the true target coefficient list. -/
def targetModFingerprint (modulus : Int) (coeffs : List Int) : Int :=
  polynomialAt3 coeffs % modulus

/-- Both exact target lists equal implies both modular fingerprints
    equal, so any mismatch safely rules out the target equality. -/
theorem authenticated_target_fingerprint_disagreement
    (proposal target : List Int)
    (h : targetModFingerprint modulusP proposal ≠
        targetModFingerprint modulusP target ∨
      targetModFingerprint modulusQ proposal ≠
        targetModFingerprint modulusQ target) :
    proposal ≠ target := by
  intro same
  subst target
  exact h.elim (fun false => false rfl) (fun false => false rfl)

/-- Exactly the recursively computed weight of a terminal coefficient
    at evaluation point r=3. This avoids assumptions about a power-tactic
    library and matches the polynomial evaluator definition. -/
def terminalWeight : Nat → Int
  | 0 => 1
  | n + 1 => evaluationPoint * terminalWeight n

/-- Appending a final coefficient change of delta to a polynomial of
    arbitrary length changes evaluation at r=3 by exactly delta*r^n.
    This is the exact source-independent perturbation used at the
    last hidden future coefficient of degree 768 or 1536. -/
theorem polynomial_terminal_shift_at_three
    (coeffPrefix : List Int) (last delta : Int) :
    polynomialAt3 (coeffPrefix ++ [last+delta]) =
      polynomialAt3 (coeffPrefix ++ [last]) +
        terminalWeight coeffPrefix.length*delta := by
  induction coeffPrefix with
  | nil =>
      simp [polynomialAt3, terminalWeight]
  | cons a rest ih =>
      simp only [List.cons_append, List.length_cons, polynomialAt3]
      rw [ih]
      simp only [terminalWeight]
      rw [Int.mul_add]
      ac_rfl

/-- A full p-step in the LAST coefficient is invisible to the
    authenticated p fingerprint at any public query degree. -/
theorem polynomial_terminal_p_collision
    (coeffPrefix : List Int) (last : Int) :
    targetModFingerprint modulusP (coeffPrefix ++ [last+modulusP]) =
      targetModFingerprint modulusP (coeffPrefix ++ [last]) := by
  unfold targetModFingerprint
  rw [polynomial_terminal_shift_at_three]
  unfold modulusP
  omega

/-- A full p*q-step in the LAST coefficient evades BOTH authenticated
    short modular fingerprints at every finite query degree. -/
theorem polynomial_terminal_double_collision
    (coeffPrefix : List Int) (last : Int) :
    targetModFingerprint modulusP
      (coeffPrefix ++ [last+modulusP*modulusQ]) =
      targetModFingerprint modulusP (coeffPrefix ++ [last]) ∧
    targetModFingerprint modulusQ
      (coeffPrefix ++ [last+modulusP*modulusQ]) =
      targetModFingerprint modulusQ (coeffPrefix ++ [last]) := by
  unfold targetModFingerprint
  constructor
  · rw [polynomial_terminal_shift_at_three]
    unfold modulusP modulusQ
    omega
  · rw [polynomial_terminal_shift_at_three]
    unfold modulusP modulusQ
    omega

#print axioms polynomial_terminal_shift_at_three
#print axioms polynomial_terminal_p_collision
#print axioms polynomial_terminal_double_collision

#print axioms authentic_fingerprint_mismatch_proves_wrong_target
#print axioms authenticated_fingerprint_equal_and_injective_is_sound
#print axioms self_generated_commitment_is_vacuous
#print axioms indistinguishable_public_and_commitment_worlds
#print axioms single_modulus_period_collision
#print axioms double_modulus_product_collision
#print axioms unit_shift_changes_first_modulus
#print axioms p_shift_changes_second_modulus
#print axioms collision_is_distinct_future
#print axioms authenticated_target_fingerprint_disagreement

end MathCan.NOR22ModularFutureCommitments
