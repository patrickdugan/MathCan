import MathCan.PairedHistory

/-!
PEF-07: exact context-closed source ceiling and old-bit coalition signatures.

A complete 4-bit old-history hypercube is repeated for each context.
Any predictor using only the context must output one fixed label on all
16 focal assignments. The source-only optimal correct counts are 10
of 16 for XOR of two AND gates, and 11 of 16 for the additive-score
threshold at two. This is the algebraic foundation of the PEF-07
12-bit disjoint-context neural train/probe/heldout split.

These are *finite* source-fibre and threshold-control statements.
They make no assertion of pretrained-model generalization.
-/

namespace MathCan.CoalitionContextBound

/-- Input bits of a four-bit history, least significant first. -/
def bit (w : Fin 16) (index : Nat) : Nat :=
  (w.val / (2^index)) % 2

/-- Positive only when exactly one of the two disjoint AND gates fires. -/
def coalition (w : Fin 16) : Bool :=
  decide ((bit w 0 * bit w 1 + bit w 2 * bit w 3) % 2 = 1)

/-- Boolean threshold of an additive four-bit score at 2. -/
def threshold (w : Fin 16) : Bool :=
  decide (2 ≤ bit w 0 + bit w 1 + bit w 2 + bit w 3)

def additiveScore (w : Fin 16) : Nat :=
  bit w 0 + bit w 1 + bit w 2 + bit w 3

/-- Exact count among the 16 possible old-history assignments
    when the prediction is independent of those four bits. -/
def correctCount (prediction : Bool) (teacher : Fin 16 → Bool) : Nat :=
  ((List.finRange 16).filter (fun w => prediction == teacher w)).length

/-- The coalition label has six positives and ten negatives. -/
theorem coalitionSixPositive :
    correctCount true coalition = 6 ∧
    correctCount false coalition = 10 := by
  decide

/-- The additive-threshold label has eleven positives and five negatives. -/
theorem thresholdElevenPositive :
    correctCount true threshold = 11 ∧
    correctCount false threshold = 5 := by
  decide

/-- No context-only Boolean prediction can outperform 10 of
    the 16 complete old-history assignments on the coalition task. -/
theorem coalitionContextOnlyCeiling (prediction : Bool) :
    correctCount prediction coalition ≤ 10 := by
  cases prediction <;> decide

/-- The analogous source-only ceiling for the threshold task is 11. -/
theorem thresholdContextOnlyCeiling (prediction : Bool) :
    correctCount prediction threshold ≤ 11 := by
  cases prediction <;> decide

/-- Any function depending only on the context obeys the 10/16
    ceiling on each complete sixteen-state old-history fibre. -/
theorem anyContextPredictorCoalitionBound
    {Context : Type} (predict : Context → Bool) (c : Context) :
    correctCount (predict c) coalition ≤ 10 :=
  coalitionContextOnlyCeiling (predict c)

theorem anyContextPredictorThresholdBound
    {Context : Type} (predict : Context → Bool) (c : Context) :
    correctCount (predict c) threshold ≤ 11 :=
  thresholdContextOnlyCeiling (predict c)

/-- The context-only limit accumulates over any finite list of
    complete 16-cell source groups, irrespective of context labels. -/
theorem anyListOfCoalitionContexts
    {Context : Type} (predict : Context → Bool)
    (contexts : List Context) :
    ((contexts.map (fun c => correctCount (predict c) coalition)).sum)
      ≤ 10 * contexts.length := by
  induction contexts with
  | nil =>
      simp
  | cons c rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have localBound := anyContextPredictorCoalitionBound predict c
      omega

theorem anyListOfThresholdContexts
    {Context : Type} (predict : Context → Bool)
    (contexts : List Context) :
    ((contexts.map (fun c => correctCount (predict c) threshold)).sum)
      ≤ 11 * contexts.length := by
  induction contexts with
  | nil =>
      simp
  | cons c rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have localBound := anyContextPredictorThresholdBound predict c
      omega

/-- At four-bit source zero every singleton flip is inactive
    for both teachers. -/
theorem fourIndividualFlipsInactive :
    (∀ i : Fin 4, coalition (⟨2^i.val, by decide⟩ : Fin 16) = false) := by
  decide

/-- The two disjoint complete AND pairs activate the coalition
    label; all four cross-pairs remain inactive at zero. -/
theorem exactTwoCoalitionPairs :
    coalition (0 : Fin 16) = false ∧
    coalition (3 : Fin 16) = true ∧
    coalition (12 : Fin 16) = true ∧
    coalition (5 : Fin 16) = false ∧
    coalition (9 : Fin 16) = false ∧
    coalition (6 : Fin 16) = false ∧
    coalition (10 : Fin 16) = false := by
  decide

/-- Every two-bit flip activates the threshold label at zero. -/
theorem allSixThresholdPairs :
    threshold (0 : Fin 16) = false ∧
    threshold (3 : Fin 16) = true ∧
    threshold (5 : Fin 16) = true ∧
    threshold (9 : Fin 16) = true ∧
    threshold (6 : Fin 16) = true ∧
    threshold (10 : Fin 16) = true ∧
    threshold (12 : Fin 16) = true := by
  decide

/-- The threshold teacher's *prethreshold* arithmetic score is
    additive: its two-bit four-corner change vanishes. -/
theorem additiveTeacherHasZeroMixedTerm :
    additiveScore (3 : Fin 16) + additiveScore (0 : Fin 16) =
       additiveScore (1 : Fin 16) + additiveScore (2 : Fin 16) ∧
    additiveScore (12 : Fin 16) + additiveScore (0 : Fin 16) =
       additiveScore (4 : Fin 16) + additiveScore (8 : Fin 16) ∧
    additiveScore (5 : Fin 16) + additiveScore (0 : Fin 16) =
       additiveScore (1 : Fin 16) + additiveScore (4 : Fin 16) := by
  decide

/-- Exact arithmetic source ceilings on the 48 heldout contexts. -/
theorem fortyEightContextSourceCeilings :
    48 * 16 = 768 ∧ 48 * 10 = 480 ∧ 48 * 11 = 528 := by
  decide

#print axioms coalitionSixPositive
#print axioms thresholdElevenPositive
#print axioms coalitionContextOnlyCeiling
#print axioms thresholdContextOnlyCeiling
#print axioms anyContextPredictorCoalitionBound
#print axioms anyContextPredictorThresholdBound
#print axioms anyListOfCoalitionContexts
#print axioms anyListOfThresholdContexts
#print axioms exactTwoCoalitionPairs
#print axioms allSixThresholdPairs
#print axioms additiveTeacherHasZeroMixedTerm
#print axioms fortyEightContextSourceCeilings

end MathCan.CoalitionContextBound
