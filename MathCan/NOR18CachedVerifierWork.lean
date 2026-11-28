import Init

/-!
# NOR-18: source-prefix sieve nesting and cached four-operation work

RRC25 enumerates sixteen U/V candidate pairs from four unary operators.
The separate exact checker computes base, U, V anew for each candidate.
The cached batch checker computes four unary maps once per demonstration
and shares them across all sixteen candidate combinations.

At any fixed degree, write u = sum of the four unary map costs,
b = the base map cost, and c = one candidate composition+comparison
cost. For the sixteen ordered candidate pairs, separate unary work is
16*b + 8*u. Cached unary work is u. With two demonstrations, the
cached screen saves exactly 2*(16*b + 7*u) coefficient-work units.
This is an arithmetic proxy, not a big-integer bit complexity or
wall-clock statement.

Public rejection by an exact prefix is monotone: once two source
sequences disagree at a shorter prefix, they remain incompatible at
every longer prefix. This guarantees that sound larger-depth public
sieves leave weakly fewer candidate programs.

These finite facts accompany the source-locked NOR-18 empirical sweep.
They do not establish a particular depth's practical cost superiority,
and they do not import held-out future outputs into the verifier.
-/

namespace MathCan.NOR18CachedVerifierWork

universe u

/-- Agreement on the first n elements of two finite sequences. -/
def agreesPrefix {Alpha : Type u} (a b : List Alpha) (n : Nat) : Prop :=
  a.take n = b.take n

/-- Agreement at any long prefix implies agreement at every shorter
    prefix. This holds for arbitrary finite coefficient sequences. -/
theorem prefix_agreement_refines
    {Alpha : Type u}
    (a b : List Alpha)
    (short long : Nat)
    (hShortLong : short ≤ long)
    (hLong : agreesPrefix a b long) :
    agreesPrefix a b short := by
  unfold agreesPrefix at *
  have congr := congrArg (fun xs : List Alpha => xs.take short) hLong
  simpa [List.take_take, Nat.min_eq_left hShortLong] using congr

/-- A candidate eliminated by a short exact prefix remains eliminated
    under every longer exact prefix test. -/
theorem prefix_rejection_persists
    {Alpha : Type u}
    (a b : List Alpha)
    (short long : Nat)
    (hShortLong : short ≤ long)
    (hReject : ¬ agreesPrefix a b short) :
    ¬ agreesPrefix a b long := by
  intro hLong
  exact hReject (prefix_agreement_refines a b short long hShortLong hLong)

/-- A sound long-depth sieve is a subset of a sound short-depth sieve,
    provided each candidate's prefix test compares the same public
    finite sequences. -/
theorem longer_public_screen_refines_possible_candidates
    {Candidate : Type u}
    (predicted observed : Candidate → List Nat)
    (short long : Nat)
    (hShortLong : short ≤ long)
    (c : Candidate)
    (hLong : agreesPrefix (predicted c) (observed c) long) :
    agreesPrefix (predicted c) (observed c) short := by
  exact prefix_agreement_refines
    (predicted c) (observed c) short long hShortLong hLong

/-- Per two public demonstrations, the proxy cost of computing all 16
    candidates separately, with one base map used by every candidate and
    each of four U/V maps used eight times across the 4x4 family. -/
def independentSixteenWork
    (baseOp sumFourUnary oneComposition : Nat) : Nat :=
  2 * (16*baseOp + 8*sumFourUnary + 16*oneComposition)

/-- Cache each of four unary maps once per public demonstration,
    keeping the same 16 candidate composition/comparison operations. -/
def cachedSixteenWork
    (sumFourUnary oneComposition : Nat) : Nat :=
  2 * (sumFourUnary + 16*oneComposition)

/-- Exact cost saving induced by the 4x4 U/V sharing pattern. -/
theorem sixteen_pair_cache_work_identity
    (baseOp sumFourUnary oneComposition : Nat) :
    independentSixteenWork baseOp sumFourUnary oneComposition =
      cachedSixteenWork sumFourUnary oneComposition +
        2*(16*baseOp+7*sumFourUnary) := by
  simp only [independentSixteenWork,cachedSixteenWork]
  omega

/-- Cached full-degree screening requires at most the total arithmetic
    work of running every sixteen exact public checks independently. -/
theorem cached_full_screen_never_costs_more
    (baseOp sumFourUnary oneComposition : Nat) :
    cachedSixteenWork sumFourUnary oneComposition ≤
      independentSixteenWork baseOp sumFourUnary oneComposition := by
  have h := sixteen_pair_cache_work_identity
    baseOp sumFourUnary oneComposition
  omega

/-- With one or more positive base/unary operation costs, the complete
    independent sixteen-check batch has strictly more proxy work. -/
theorem cached_full_screen_strictly_cheaper
    (baseOp sumFourUnary oneComposition : Nat)
    (hPositive : 0 < baseOp ∨ 0 < sumFourUnary) :
    cachedSixteenWork sumFourUnary oneComposition <
      independentSixteenWork baseOp sumFourUnary oneComposition := by
  have h := sixteen_pair_cache_work_identity
    baseOp sumFourUnary oneComposition
  rcases hPositive with hb | hu
  · omega
  · omega

/-- An exact work cap can admit a cached batch and exclude the
    independent candidate-by-candidate implementation. Query simulation
    work is charged to both sides equally in this comparison. -/
theorem cache_can_fit_when_separate_checks_exceed_cap
    (baseOp sumFourUnary oneComposition queryWork budget : Nat)
    (hFits : queryWork +
      cachedSixteenWork sumFourUnary oneComposition ≤ budget)
    (hTooMuch : budget < queryWork +
      independentSixteenWork baseOp sumFourUnary oneComposition) :
    (queryWork+cachedSixteenWork sumFourUnary oneComposition ≤ budget) ∧
      ¬ (queryWork +
        independentSixteenWork baseOp sumFourUnary oneComposition ≤ budget) := by
  constructor
  · exact hFits
  · omega

/-- The required fully budgeted proof certificate is a conjunction of
    public semantic validity and a finite arithmetic work allowance. -/
theorem costed_public_certificate_sound
    {Candidate : Type u}
    (trueCompatible remaining : Candidate → Prop)
    (hypotheticalFuture : Candidate → Nat)
    (planted accepted : Candidate)
    (work budget : Nat)
    (trueInFamily : trueCompatible planted)
    (soundRemaining : ∀ p, trueCompatible p → remaining p)
    (acceptedRemaining : remaining accepted)
    (unanimous : ∀ p, remaining p →
      hypotheticalFuture p = hypotheticalFuture accepted)
    (withinBudget : work ≤ budget) :
    work ≤ budget ∧
      hypotheticalFuture planted = hypotheticalFuture accepted := by
  constructor
  · exact withinBudget
  · exact unanimous planted (soundRemaining planted trueInFamily)

#print axioms prefix_agreement_refines
#print axioms prefix_rejection_persists
#print axioms longer_public_screen_refines_possible_candidates
#print axioms sixteen_pair_cache_work_identity
#print axioms cached_full_screen_never_costs_more
#print axioms cached_full_screen_strictly_cheaper
#print axioms cache_can_fit_when_separate_checks_exceed_cap
#print axioms costed_public_certificate_sound

end MathCan.NOR18CachedVerifierWork
