import Init
import ContinuityV1.Refinement
import ContinuityV1.AdapterSuccession

/-!
# SelfModels continuity: initial kernel obligations

This self-contained module formalizes small, explicit invariants of the proposed
interface. In particular, the canonical-stream result is about *excluding*
interpretive annotations, not an implementation-refinement proof for the Python
DAG evaluator. The more ambitious probability, Hessian, and arbitrary-k
subset-count theorems remain in THEOREMS.md awaiting formalization.
-/

namespace SelfModels.ContinuityV1

/-- The four record categories used by the Python finite reference. -/
inductive Record where
  | assertion (eid : Nat) (claim : String)
  | derivation (eid : Nat) (claim : String) (premises : List Nat)
  | retraction (eid : Nat) (target : Nat)
  | interpretation (eid : Nat) (modelVersion : String) (note : String)
  deriving Repr, DecidableEq

/-- Strip interpretation-only records, retaining the order of canonical records. -/
def canonicalStream : List Record → List Record
  | [] => []
  | Record.interpretation _ _ _ :: tail => canonicalStream tail
  | record :: tail => record :: canonicalStream tail

/-- Appending an interpretation cannot change the canonical input stream. -/
theorem append_interpretation_invariant
    (records : List Record) (eid : Nat) (version note : String) :
    canonicalStream (records ++ [Record.interpretation eid version note]) =
      canonicalStream records := by
  induction records with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp [canonicalStream, ih]

/-- Canonical extraction is idempotent. -/
theorem canonicalStream_idempotent (records : List Record) :
    canonicalStream (canonicalStream records) = canonicalStream records := by
  induction records with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp [canonicalStream, ih]

/-- The trusted host decides support membership; a learned scorer only ranks it. -/
def certifiedActions (actions : List String) (admitted : String → Bool) : List String :=
  actions.filter admitted

/-- No persona reweighting can grant membership outside the admitted set. -/
theorem certified_action_admitted
    (actions : List String) (admitted : String → Bool) (a : String)
    (h : a ∈ certifiedActions actions admitted) : admitted a = true := by
  have hf : a ∈ actions ∧ admitted a = true := by
    simpa [certifiedActions] using h
  exact hf.2

/-- This is the exact loss-of-margin counterexample with margins scaled by 4. -/
def marginNumerator (a b : Int) : Int := 1 - 4 * a * b

theorem separate_updates_look_harmless :
    marginNumerator 0 0 = 1 ∧
    marginNumerator 1 0 = 1 ∧
    marginNumerator 0 1 = 1 := by
  decide

theorem combined_updates_reverse_margin : marginNumerator 1 1 = -3 := by
  decide

/-- In the 9/10 survival example, coupling four steps loses at most 3439/10000. -/
theorem coupling_four_step_numerators : (10000 : Nat) - 9 ^ 4 = 3439 := by
  decide

/-- The two rational 2D vectors from SAU-CURVE02's finite witness have unit norm. -/
theorem near_collinear_integer_identity :
    (9999 : Nat) ^ 2 + 200 ^ 2 = 10001 ^ 2 := by
  decide

/-- Their unit-column Gram gap is 2/10001, hence nearly singular. -/
theorem coactive_gram_numerator_gap : (10001 : Nat) - 9999 = 2 := by
  decide

end SelfModels.ContinuityV1
