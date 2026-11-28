import Init

/-!
# NOR-15C: exact public-verifier aliasing and first-accepted decisions

A representation-only ranker receives the same source tensor on two cases.
The native verifier then visits a fixed ordered candidate list and stops
at the first candidate accepted by the public demonstration check.

The following propositions are independent of the concrete 16-candidate
RRC25 model. They formalize the precise obstruction under *identical full
public acceptance masks*: identical observable masks force the selected
candidate to agree, and disjoint future-correct sets then prevent both
cases from succeeding.

These statements are exact finite decision-list mathematics. The companion
empirical audit uses 16 public candidate checks per test case and withheld
future labels for a retrospective, non-deployable hindsight bound.
-/

namespace MathCan.NOR15VerifierAlias

universe u

/-- The candidate selected by a fixed ordered public verifier.
    The first public-accepted template is returned, otherwise none. -/
def firstAccepted {Candidate : Type u} :
    List Candidate → (Candidate → Bool) → Option Candidate
  | [], _ => none
  | j :: remaining, accepts =>
      if accepts j = true then some j
      else firstAccepted remaining accepts

/-- The first-public-acceptance rule is determined entirely by the
    ordered candidate list and the complete public acceptance mask. -/
theorem firstAccepted_congr
    {Candidate : Type u}
    (order : List Candidate)
    (acceptA acceptB : Candidate → Bool)
    (h : ∀ j, acceptA j = acceptB j) :
    firstAccepted order acceptA = firstAccepted order acceptB := by
  induction order with
  | nil =>
      rfl
  | cons j rest ih =>
      simp [firstAccepted, h j, ih]

/-- If the first verifier accepts class j in case A and the two
    acceptance signatures agree, it accepts the same class in B. -/
theorem identical_public_masks_force_same_first_success
    {Candidate : Type u}
    (order : List Candidate)
    (acceptA acceptB : Candidate → Bool)
    (j : Candidate)
    (sameMask : ∀ c, acceptA c = acceptB c)
    (acceptedA : firstAccepted order acceptA = some j) :
    firstAccepted order acceptB = some j := by
  exact (firstAccepted_congr order acceptA acceptB sameMask).symm.trans acceptedA

/-- When two future-correct sets are disjoint, one of the two
    predictions must fail for any common selected candidate. -/
theorem disjoint_futures_force_one_failure
    {Candidate : Type u}
    (futureA futureB : Candidate → Bool)
    (disjoint : ∀ c, futureA c = true → futureB c = false)
    (j : Candidate) :
    futureA j = false ∨ futureB j = false := by
  cases ha : futureA j with
  | false =>
      exact Or.inl rfl
  | true =>
      exact Or.inr (disjoint j ha)

/-- The full alias obstruction: under identical public acceptance
    responses, a fixed stop-at-first-success verifier picks the same
    template. If that template is future-correct in at most one source,
    at least one source must fail its future evaluation. -/
theorem identical_masks_disjoint_truth_alias_obstruction
    {Candidate : Type u}
    (order : List Candidate)
    (acceptA acceptB futureA futureB : Candidate → Bool)
    (j : Candidate)
    (sameMask : ∀ c, acceptA c = acceptB c)
    (disjoint : ∀ c, futureA c = true → futureB c = false)
    (acceptedA : firstAccepted order acceptA = some j) :
    firstAccepted order acceptB = some j ∧
      (futureA j = false ∨ futureB j = false) := by
  constructor
  · exact identical_public_masks_force_same_first_success
      order acceptA acceptB j sameMask acceptedA
  · exact disjoint_futures_force_one_failure futureA futureB disjoint j

#print axioms firstAccepted_congr
#print axioms identical_public_masks_force_same_first_success
#print axioms disjoint_futures_force_one_failure
#print axioms identical_masks_disjoint_truth_alias_obstruction

end MathCan.NOR15VerifierAlias
