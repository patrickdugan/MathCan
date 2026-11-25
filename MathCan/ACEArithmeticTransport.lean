import Init

/-!
ACE-02: transport of first-order arithmetic satisfaction across
an isomorphism, with explicit de Bruijn binding and scoping.
The intended L/V application additionally needs a model construction
and an object-theory translation. Neither is assumed here.
-/
namespace MathCan.ACE.Arithmetic
universe u v

structure Model (A : Type u) where
  zero : A
  succ : A → A
  add : A → A → A
  mul : A → A → A
  lt : A → A → Prop

structure Iso {A : Type u} {B : Type v} (M : Model A) (N : Model B) where
  map : A → B
  inj : ∀ {a b : A}, map a = map b → a = b
  onto : ∀ b : B, ∃ a : A, map a = b
  zero_eq : map M.zero = N.zero
  succ_eq : ∀ a, map (M.succ a) = N.succ (map a)
  add_eq : ∀ a b, map (M.add a b) = N.add (map a) (map b)
  mul_eq : ∀ a b, map (M.mul a b) = N.mul (map a) (map b)
  lt_iff : ∀ a b, M.lt a b ↔ N.lt (map a) (map b)

inductive Term where
  | var : Nat → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term

inductive Formula where
  | falsum : Formula
  | eq : Term → Term → Formula
  | lt : Term → Term → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  | all : Formula → Formula
  | ex : Formula → Formula

def push {A : Type u} (a : A) (ρ : Nat → A) : Nat → A
  | 0 => a
  | i + 1 => ρ i

def Term.scoped (k : Nat) : Term → Prop
  | .var i => i < k
  | .zero => True
  | .succ t => scoped k t
  | .add t s => scoped k t ∧ scoped k s
  | .mul t s => scoped k t ∧ scoped k s

def Formula.scoped (k : Nat) : Formula → Prop
  | .falsum => True
  | .eq t s => t.scoped k ∧ s.scoped k
  | .lt t s => t.scoped k ∧ s.scoped k
  | .conj p q => scoped k p ∧ scoped k q
  | .disj p q => scoped k p ∧ scoped k q
  | .impl p q => scoped k p ∧ scoped k q
  | .all p => scoped (k + 1) p
  | .ex p => scoped (k + 1) p

def Sentence := {p : Formula // p.scoped 0}

def Term.eval {A : Type u} (M : Model A) (ρ : Nat → A) : Term → A
  | .var i => ρ i
  | .zero => M.zero
  | .succ t => M.succ (eval M ρ t)
  | .add t s => M.add (eval M ρ t) (eval M ρ s)
  | .mul t s => M.mul (eval M ρ t) (eval M ρ s)

def Formula.sat {A : Type u} (M : Model A) (ρ : Nat → A) : Formula → Prop
  | .falsum => False
  | .eq t s => t.eval M ρ = s.eval M ρ
  | .lt t s => M.lt (t.eval M ρ) (s.eval M ρ)
  | .conj p q => sat M ρ p ∧ sat M ρ q
  | .disj p q => sat M ρ p ∨ sat M ρ q
  | .impl p q => sat M ρ p → sat M ρ q
  | .all p => ∀ a : A, sat M (push a ρ) p
  | .ex p => ∃ a : A, sat M (push a ρ) p

variable {A : Type u} {B : Type v}

theorem push_transport {M : Model A} {N : Model B} (e : Iso M N)
    {ρ : Nat → A} {σ : Nat → B} (h : ∀ i, e.map (ρ i) = σ i)
    {a : A} {b : B} (hab : e.map a = b) :
    ∀ i, e.map (push a ρ i) = push b σ i := by
  intro i
  cases i with
  | zero => exact hab
  | succ i => exact h i

theorem eval_transport {M : Model A} {N : Model B} (e : Iso M N)
    (ρ : Nat → A) (σ : Nat → B) (h : ∀ i, e.map (ρ i) = σ i)
    (t : Term) : e.map (t.eval M ρ) = t.eval N σ := by
  induction t with
  | var i => exact h i
  | zero => exact e.zero_eq
  | succ t ih => simp only [Term.eval, e.succ_eq, ih]
  | add t s iht ihs => simp only [Term.eval, e.add_eq, iht, ihs]
  | mul t s iht ihs => simp only [Term.eval, e.mul_eq, iht, ihs]

theorem sat_transport {M : Model A} {N : Model B} (e : Iso M N)
    (p : Formula) (ρ : Nat → A) (σ : Nat → B)
    (h : ∀ i, e.map (ρ i) = σ i) :
    p.sat M ρ ↔ p.sat N σ := by
  induction p generalizing ρ σ with
  | falsum => exact Iff.rfl
  | eq t s =>
    change (t.eval M ρ = s.eval M ρ) ↔ (t.eval N σ = s.eval N σ)
    rw [← eval_transport e ρ σ h t, ← eval_transport e ρ σ h s]
    exact ⟨fun heq => congrArg e.map heq, fun heq => e.inj heq⟩
  | lt t s =>
    change M.lt (t.eval M ρ) (s.eval M ρ) ↔ N.lt (t.eval N σ) (s.eval N σ)
    rw [← eval_transport e ρ σ h t, ← eval_transport e ρ σ h s]
    exact e.lt_iff _ _
  | conj p q ihp ihq =>
    simp only [Formula.sat, ihp ρ σ h, ihq ρ σ h]
  | disj p q ihp ihq =>
    simp only [Formula.sat, ihp ρ σ h, ihq ρ σ h]
  | impl p q ihp ihq =>
    simp only [Formula.sat, ihp ρ σ h, ihq ρ σ h]
  | all p ih =>
    change (∀ a : A, p.sat M (push a ρ)) ↔ (∀ b : B, p.sat N (push b σ))
    constructor
    · intro hp b
      obtain ⟨a, ha⟩ := e.onto b
      exact (ih (push a ρ) (push b σ) (push_transport e h ha)).mp (hp a)
    · intro hp a
      exact (ih (push a ρ) (push (e.map a) σ)
        (push_transport e h rfl)).mpr (hp (e.map a))
  | ex p ih =>
    change (∃ a : A, p.sat M (push a ρ)) ↔ (∃ b : B, p.sat N (push b σ))
    constructor
    · intro hp
      obtain ⟨a, ha⟩ := hp
      exact ⟨e.map a, (ih (push a ρ) (push (e.map a) σ)
        (push_transport e h rfl)).mp ha⟩
    · intro hp
      obtain ⟨b, hb⟩ := hp
      obtain ⟨a, ha⟩ := e.onto b
      exact ⟨a, (ih (push a ρ) (push b σ) (push_transport e h ha)).mpr hb⟩

def Sentence.sat (M : Model A) (p : Sentence) : Prop :=
  p.val.sat M (fun _ => M.zero)

theorem sentence_transport {M : Model A} {N : Model B} (e : Iso M N)
    (p : Sentence) : p.sat M ↔ p.sat N :=
  sat_transport e p.val (fun _ => M.zero) (fun _ => N.zero) (fun _ => e.zero_eq)

#print axioms push_transport
#print axioms eval_transport
#print axioms sat_transport
#print axioms sentence_transport

end MathCan.ACE.Arithmetic
