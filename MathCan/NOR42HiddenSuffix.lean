import MathCan.NOR40SingletonBracket

/-!
NOR-42 design companion: formal indistinguishability of late-suffix native
programs from public finite-series prefixes.

For a source with publicly visible output coefficients through degree D, add
a hidden term β X^(D+32) T(F), where T(F) has constant coefficient one and
β is a nonzero integer. The first changed output is exactly D+32; the
observed output coefficients 0..D remain equal.

An estimator whose only target-output input is the common public prefix
must make the same prediction for both candidate future worlds. It therefore
cannot be exactly correct for both. An externally authenticated full target
output is a separate additional information source.

All theorems are source-general, use no random coins and claim no learned
model performance or actual existence of a deployed future oracle.
-/

namespace MathCan.NOR42HiddenSuffix

/-- Coefficientwise native hidden-suffix construction. The term is zero
    before onset and equals β times a shifted unit transform afterwards. -/
def hiddenOutput (onset : Nat) (beta : Int)
    (transform clean : Nat → Int) (index : Nat) : Int :=
  if onset ≤ index then
    clean index + beta * transform (index - onset)
  else
    clean index

/-- The hidden mechanism is exactly invisible at all earlier coefficients. -/
theorem hidden_before_onset
    (onset index : Nat) (beta : Int)
    (transform clean : Nat → Int)
    (before : index < onset) :
    hiddenOutput onset beta transform clean index = clean index := by
  have h : ¬ onset ≤ index := by omega
  simp [hiddenOutput, h]

/-- The first difference has size β, given the unit-series normalization
    of the hidden transform's constant coefficient. -/
theorem first_hidden_coefficient
    (onset : Nat) (beta : Int)
    (transform clean : Nat → Int)
    (constant : transform 0 = 1) :
    hiddenOutput onset beta transform clean onset =
      clean onset + beta := by
  simp [hiddenOutput, constant]

/-- The hidden target changes at onset whenever β is nonzero. -/
theorem first_hidden_coefficient_differs
    (onset : Nat) (beta : Int)
    (transform clean : Nat → Int)
    (constant : transform 0 = 1)
    (nonzero : beta ≠ 0) :
    hiddenOutput onset beta transform clean onset ≠ clean onset := by
  rw [first_hidden_coefficient onset beta transform clean constant]
  intro equal
  omega

/-- The publicly observable finite prefix is the map on indices 0..D. -/
def publicPrefix (degree : Nat) (output : Nat → Int) :
    Fin (degree + 1) → Int :=
  fun i => output i.val

/-- A hidden shift starting at D+32 cannot affect any of the D+1 public
    output coefficients, even when its eventual future differs. -/
theorem same_public_prefix
    (degree : Nat) (beta : Int)
    (transform clean : Nat → Int) :
    publicPrefix degree
      (hiddenOutput (degree + 32) beta transform clean) =
    publicPrefix degree clean := by
  funext i
  dsimp [publicPrefix]
  apply hidden_before_onset
  have hi := i.isLt
  omega

/-- The complete future functions differ, even though their public
    target-output prefixes are exactly equal. -/
theorem future_functions_differ
    (degree : Nat) (beta : Int)
    (transform clean : Nat → Int)
    (constant : transform 0 = 1)
    (nonzero : beta ≠ 0) :
    hiddenOutput (degree + 32) beta transform clean ≠ clean := by
  intro eqfun
  have heq := congrArg
    (fun f : Nat → Int => f (degree + 32)) eqfun
  exact (first_hidden_coefficient_differs
    (degree + 32) beta transform clean constant nonzero) heq

/-- Any deterministic estimator with access only to the public target
    prefix produces exactly the same candidate for both paired worlds. -/
theorem public_predictor_has_identical_output
    (degree : Nat) (beta : Int)
    (transform clean : Nat → Int)
    (predict : (Fin (degree + 1) → Int) → (Nat → Int)) :
    predict (publicPrefix degree clean) =
    predict (publicPrefix degree
      (hiddenOutput (degree + 32) beta transform clean)) := by
  rw [same_public_prefix]

/-- A single public-prefix-based predictor cannot match both true future
    sequences when they differ after the visible interval. -/
theorem public_predictor_cannot_match_both
    (degree : Nat) (beta : Int)
    (transform clean : Nat → Int)
    (predict : (Fin (degree + 1) → Int) → (Nat → Int))
    (constant : transform 0 = 1)
    (nonzero : beta ≠ 0) :
    ¬ (predict (publicPrefix degree clean) = clean ∧
       predict (publicPrefix degree
         (hiddenOutput (degree + 32) beta transform clean)) =
         hiddenOutput (degree + 32) beta transform clean) := by
  intro both
  have same := public_predictor_has_identical_output
    degree beta transform clean predict
  have equalFutures :
      clean = hiddenOutput (degree + 32) beta transform clean := by
    calc
      clean = predict (publicPrefix degree clean) := both.1.symm
      _ = predict (publicPrefix degree
            (hiddenOutput (degree + 32) beta transform clean)) := same
      _ = hiddenOutput (degree + 32) beta transform clean := both.2
  exact (future_functions_differ degree beta transform clean
    constant nonzero) equalFutures.symm

#print axioms hidden_before_onset
#print axioms first_hidden_coefficient
#print axioms first_hidden_coefficient_differs
#print axioms same_public_prefix
#print axioms future_functions_differ
#print axioms public_predictor_has_identical_output
#print axioms public_predictor_cannot_match_both

end MathCan.NOR42HiddenSuffix
