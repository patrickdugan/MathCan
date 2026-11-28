import Init

/-!
ACE-01: finite selection is admissible constructively.
These are native Lean theorems, not a formalization of ZF/ZFC.
The classical comparison uses a global selector; the replacement
only eliminates choice for the finite list in the conclusion.
-/

namespace MathCan.ACE

universe u v
variable {α : Type u} {β : Type v}

inductive Aligned (R : α → β → Prop) : List α → List β → Prop where
  | nil : Aligned R [] []
  | cons {a : α} {b : β} {xs : List α} {ys : List β} :
      R a b → Aligned R xs ys → Aligned R (a :: xs) (b :: ys)

/-- Finite selection, even when the relation is not decidable.
The existential output is in Prop, not a computable selector in Type. -/
theorem finiteChoice (R : α → β → Prop) (xs : List α)
    (h : ∀ a, List.Mem a xs → ∃ b, R a b) :
    ∃ ys : List β, Aligned R xs ys := by
  induction xs with
  | nil => exact ⟨[], Aligned.nil⟩
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := h a (List.Mem.head xs)
    obtain ⟨ys, hys⟩ := ih (fun i hi => h i (List.Mem.tail a hi))
    exact ⟨b :: ys, Aligned.cons hb hys⟩

theorem alignedMap (R : α → β → Prop) (f : α → β)
    (h : ∀ a, R a (f a)) (xs : List α) :
    Aligned R xs (xs.map f) := by
  induction xs with
  | nil => exact Aligned.nil
  | cons a xs ih => exact Aligned.cons (h a) ih

/-- Source proof: the global choice function is stronger than needed. -/
theorem globalViaChoice (R : α → β → Prop) (xs : List α)
    (h : ∀ a, ∃ b, R a b) :
    ∃ ys : List β, Aligned R xs ys := by
  let f : α → β := fun a => Classical.choose (h a)
  exact ⟨xs.map f, alignedMap R f (fun a => Classical.choose_spec (h a)) xs⟩

/-- Replacement proof of precisely the same proposition. -/
theorem globalWithoutChoice (R : α → β → Prop) (xs : List α)
    (h : ∀ a, ∃ b, R a b) :
    ∃ ys : List β, Aligned R xs ys :=
  finiteChoice R xs (fun a _ => h a)

#print axioms finiteChoice
#print axioms alignedMap
#print axioms globalViaChoice
#print axioms globalWithoutChoice

end MathCan.ACE
