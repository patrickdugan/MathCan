import Init

/-!
# RHD-03: direct logical interface of the Main -> EveryCharacter -> RH route.

The published source's OpenLiteratureStatements has two fields of the
same Row proposition, and a third RecTExists field. We formalize its
exact propositional structure in Init without importing original
Mathlib proofs or identifying the mathematical Row and RecTExists types
with these abstract parameters.
-/

namespace MathCan.RHMainLogic

/-- Two copies of Row and one RecTExists proof, matching the source
interface's three fields at the level of propositions. -/
structure OpenLiteratureProxy (Row RecTExists : Prop) : Prop where
  caraianiLocalGlobalDual : Row
  localLanglandsExists : RecTExists
  galoisRepOfPolarizedPairLit : Row

/-- The duplicated Row interface is equivalent to exactly one Row
proposition together with the RecTExists proposition. -/
theorem open_literature_is_row_and_recT
    (Row RecTExists : Prop) :
    OpenLiteratureProxy Row RecTExists ↔ Row ∧ RecTExists := by
  constructor
  · intro h
    exact ⟨h.caraianiLocalGlobalDual, h.localLanglandsExists⟩
  · rintro ⟨hRow, hRec⟩
    exact ⟨hRow, hRec, hRow⟩

/-- Constructing a second Row field from the first is proof duplication
in the interface; both fields have precisely the same proposition. -/
theorem row_proof_reused
    {Row RecTExists : Prop} (hRow : Row) (hRec : RecTExists) :
    OpenLiteratureProxy Row RecTExists :=
  ⟨hRow, hRec, hRow⟩

/-- Purely structural abstract form of the source's final route.
The substantive published results remain explicit arguments. -/
theorem final_rh_route_from_supplied_mathematical_bridges
    {Row RecTExists VWin EveryCharacter RH : Prop}
    (hRow : Row) (hRec : RecTExists)
    (windowOfRow : Row → VWin)
    (everyCharacterOfLiterature : OpenLiteratureProxy Row RecTExists → VWin → EveryCharacter)
    (rhOfEvery : EveryCharacter → RH) : RH :=
  rhOfEvery (everyCharacterOfLiterature
    (row_proof_reused hRow hRec) (windowOfRow hRow))

/-- A formal literature theorem whose proof is supplied independently
can be presented with an unused O parameter. This explains the
distinction between lexical O usage and semantic dependence. -/
theorem independent_theorem_with_literature_parameter
    {Row RecTExists P : Prop}
    (p : P) (O : OpenLiteratureProxy Row RecTExists) : P :=
  p

#print axioms open_literature_is_row_and_recT
#print axioms row_proof_reused
#print axioms final_rh_route_from_supplied_mathematical_bridges
#print axioms independent_theorem_with_literature_parameter

end MathCan.RHMainLogic
