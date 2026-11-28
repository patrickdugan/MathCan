import Init

/-!
ACE-03A: semantic relativization to an explicitly given class.
A generic class predicate is not yet Goedel's constructible universe.
-/
namespace MathCan.ACE.Relativization
universe u

inductive Formula where
  | bot : Formula
  | eqv : Nat → Nat → Formula
  | mem : Nat → Nat → Formula
  | guard : Nat → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  | all : Formula → Formula
  | ex : Formula → Formula

def push {A : Type u} (a : A) (ρ : Nat → A) : Nat → A
  | 0 => a
  | i + 1 => ρ i

def Formula.restrict : Formula → Formula
  | .bot => .bot
  | .eqv i j => .eqv i j
  | .mem i j => .mem i j
  | .guard i => .guard i
  | .conj p q => .conj p.restrict q.restrict
  | .disj p q => .disj p.restrict q.restrict
  | .impl p q => .impl p.restrict q.restrict
  | .all p => .all (.impl (.guard 0) p.restrict)
  | .ex p => .ex (.conj (.guard 0) p.restrict)

def Formula.sat {A : Type u} (E : A → A → Prop) (C : A → Prop)
    (ρ : Nat → A) : Formula → Prop
  | .bot => False
  | .eqv i j => ρ i = ρ j
  | .mem i j => E (ρ i) (ρ j)
  | .guard i => C (ρ i)
  | .conj p q => sat E C ρ p ∧ sat E C ρ q
  | .disj p q => sat E C ρ p ∨ sat E C ρ q
  | .impl p q => sat E C ρ p → sat E C ρ q
  | .all p => ∀ a : A, sat E C (push a ρ) p
  | .ex p => ∃ a : A, sat E C (push a ρ) p

variable {A : Type u} {C : A → Prop}

def subMem (E : A → A → Prop) : Subtype C → Subtype C → Prop :=
  fun a b => E a.val b.val

theorem push_agree (ρ : Nat → Subtype C) (σ : Nat → A)
    (h : ∀ i, (ρ i).val = σ i) (a : Subtype C) :
    ∀ i, (push a ρ i).val = push a.val σ i := by
  intro i
  cases i with
  | zero => rfl
  | succ i => exact h i

/-- Relativization is equivalent to satisfaction on the induced subtype.
For open formulas the assignments must agree and land in the class.
This theorem does not require choice or a selected inverse. -/
theorem sat_restrict (E : A → A → Prop) (p : Formula)
    (ρ : Nat → Subtype C) (σ : Nat → A)
    (h : ∀ i, (ρ i).val = σ i) :
    p.sat (subMem E) (fun _ => True) ρ ↔ p.restrict.sat E C σ := by
  induction p generalizing ρ σ with
  | bot => exact Iff.rfl
  | eqv i j =>
    change (ρ i = ρ j) ↔ (σ i = σ j)
    rw [← h i, ← h j]
    exact ⟨fun he => congrArg Subtype.val he, fun he => Subtype.ext he⟩
  | mem i j =>
    change E (ρ i).val (ρ j).val ↔ E (σ i) (σ j)
    rw [h i, h j]
  | guard i =>
    change True ↔ C (σ i)
    constructor
    · intro _
      rw [← h i]
      exact (ρ i).property
    · intro _
      exact True.intro
  | conj p q ihp ihq =>
    change (p.sat (subMem E) (fun _ => True) ρ ∧ q.sat (subMem E) (fun _ => True) ρ) ↔
      (p.restrict.sat E C σ ∧ q.restrict.sat E C σ)
    exact ⟨fun hpq => ⟨(ihp ρ σ h).mp hpq.1, (ihq ρ σ h).mp hpq.2⟩,
      fun hpq => ⟨(ihp ρ σ h).mpr hpq.1, (ihq ρ σ h).mpr hpq.2⟩⟩
  | disj p q ihp ihq =>
    change (p.sat (subMem E) (fun _ => True) ρ ∨ q.sat (subMem E) (fun _ => True) ρ) ↔
      (p.restrict.sat E C σ ∨ q.restrict.sat E C σ)
    constructor
    · intro hpq
      cases hpq with
      | inl hp => exact Or.inl ((ihp ρ σ h).mp hp)
      | inr hq => exact Or.inr ((ihq ρ σ h).mp hq)
    · intro hpq
      cases hpq with
      | inl hp => exact Or.inl ((ihp ρ σ h).mpr hp)
      | inr hq => exact Or.inr ((ihq ρ σ h).mpr hq)
  | impl p q ihp ihq =>
    change (p.sat (subMem E) (fun _ => True) ρ → q.sat (subMem E) (fun _ => True) ρ) ↔
      (p.restrict.sat E C σ → q.restrict.sat E C σ)
    exact ⟨fun hpq hp => (ihq ρ σ h).mp (hpq ((ihp ρ σ h).mpr hp)),
      fun hpq hp => (ihq ρ σ h).mpr (hpq ((ihp ρ σ h).mp hp))⟩
  | all p ih =>
    change (∀ a : Subtype C, p.sat (subMem E) (fun _ => True) (push a ρ)) ↔
      (∀ a : A, C a → p.restrict.sat E C (push a σ))
    constructor
    · intro hp a ha
      let b : Subtype C := ⟨a, ha⟩
      exact (ih (push b ρ) (push a σ) (push_agree ρ σ h b)).mp (hp b)
    · intro hp b
      exact (ih (push b ρ) (push b.val σ) (push_agree ρ σ h b)).mpr (hp b.val b.property)
  | ex p ih =>
    change (∃ a : Subtype C, p.sat (subMem E) (fun _ => True) (push a ρ)) ↔
      (∃ a : A, C a ∧ p.restrict.sat E C (push a σ))
    constructor
    · intro hp
      obtain ⟨b, hb⟩ := hp
      exact ⟨b.val, b.property, (ih (push b ρ) (push b.val σ) (push_agree ρ σ h b)).mp hb⟩
    · intro hp
      obtain ⟨a, ha, hp⟩ := hp
      let b : Subtype C := ⟨a, ha⟩
      exact ⟨b, (ih (push b ρ) (push a σ) (push_agree ρ σ h b)).mpr hp⟩

#print axioms push_agree
#print axioms sat_restrict
end MathCan.ACE.Relativization
