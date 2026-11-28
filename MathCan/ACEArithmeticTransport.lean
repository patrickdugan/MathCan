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

def Term.wellScoped (k : Nat) : Term → Prop
  | .var i => i < k
  | .zero => True
  | .succ t => wellScoped k t
  | .add t s => wellScoped k t ∧ wellScoped k s
  | .mul t s => wellScoped k t ∧ wellScoped k s

def Formula.wellScoped (k : Nat) : Formula → Prop
  | .falsum => True
  | .eq t s => t.wellScoped k ∧ s.wellScoped k
  | .lt t s => t.wellScoped k ∧ s.wellScoped k
  | .conj p q => wellScoped k p ∧ wellScoped k q
  | .disj p q => wellScoped k p ∧ wellScoped k q
  | .impl p q => wellScoped k p ∧ wellScoped k q
  | .all p => wellScoped (k + 1) p
  | .ex p => wellScoped (k + 1) p

def Sentence := {p : Formula // p.wellScoped 0}

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
    change (p.sat M ρ ∧ q.sat M ρ) ↔ (p.sat N σ ∧ q.sat N σ)
    exact ⟨fun hpq => ⟨(ihp ρ σ h).mp hpq.1, (ihq ρ σ h).mp hpq.2⟩,
      fun hpq => ⟨(ihp ρ σ h).mpr hpq.1, (ihq ρ σ h).mpr hpq.2⟩⟩
  | disj p q ihp ihq =>
    change (p.sat M ρ ∨ q.sat M ρ) ↔ (p.sat N σ ∨ q.sat N σ)
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
    change (p.sat M ρ → q.sat M ρ) ↔ (p.sat N σ → q.sat N σ)
    exact ⟨fun hpq hp => (ihq ρ σ h).mp (hpq ((ihp ρ σ h).mpr hp)),
      fun hpq hp => (ihq ρ σ h).mpr (hpq ((ihp ρ σ h).mp hp))⟩
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

/-- Agreement below the current binder depth survives pushing a value. -/
theorem push_local (k : Nat) (ρ σ : Nat → A)
    (h : ∀ i, i < k → ρ i = σ i) (a : A) :
    ∀ i, i < k + 1 → push a ρ i = push a σ i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact h i (Nat.lt_of_succ_lt_succ hi)

theorem eval_local (M : Model A) (t : Term) (k : Nat) (ρ σ : Nat → A)
    (hs : t.wellScoped k) (h : ∀ i, i < k → ρ i = σ i) :
    t.eval M ρ = t.eval M σ := by
  induction t generalizing k ρ σ with
  | var i => exact h i hs
  | zero => rfl
  | succ t ih => exact congrArg M.succ (ih k ρ σ hs h)
  | add t s iht ihs =>
    change t.wellScoped k ∧ s.wellScoped k at hs
    change M.add (t.eval M ρ) (s.eval M ρ) = M.add (t.eval M σ) (s.eval M σ)
    rw [iht k ρ σ hs.1 h, ihs k ρ σ hs.2 h]
  | mul t s iht ihs =>
    change t.wellScoped k ∧ s.wellScoped k at hs
    change M.mul (t.eval M ρ) (s.eval M ρ) = M.mul (t.eval M σ) (s.eval M σ)
    rw [iht k ρ σ hs.1 h, ihs k ρ σ hs.2 h]

/-- A well-wellScoped formula sees only the first k assignment entries. -/
theorem sat_local (M : Model A) (p : Formula) (k : Nat) (ρ σ : Nat → A)
    (hs : p.wellScoped k) (h : ∀ i, i < k → ρ i = σ i) :
    p.sat M ρ ↔ p.sat M σ := by
  induction p generalizing k ρ σ with
  | falsum => exact Iff.rfl
  | eq t s =>
    change t.wellScoped k ∧ s.wellScoped k at hs
    change (t.eval M ρ = s.eval M ρ) ↔ (t.eval M σ = s.eval M σ)
    rw [eval_local M t k ρ σ hs.1 h, eval_local M s k ρ σ hs.2 h]
  | lt t s =>
    change t.wellScoped k ∧ s.wellScoped k at hs
    change M.lt (t.eval M ρ) (s.eval M ρ) ↔ M.lt (t.eval M σ) (s.eval M σ)
    rw [eval_local M t k ρ σ hs.1 h, eval_local M s k ρ σ hs.2 h]
  | conj p q ihp ihq =>
    change p.wellScoped k ∧ q.wellScoped k at hs
    change (p.sat M ρ ∧ q.sat M ρ) ↔ (p.sat M σ ∧ q.sat M σ)
    exact ⟨fun hpq => ⟨(ihp k ρ σ hs.1 h).mp hpq.1, (ihq k ρ σ hs.2 h).mp hpq.2⟩,
      fun hpq => ⟨(ihp k ρ σ hs.1 h).mpr hpq.1, (ihq k ρ σ hs.2 h).mpr hpq.2⟩⟩
  | disj p q ihp ihq =>
    change p.wellScoped k ∧ q.wellScoped k at hs
    change (p.sat M ρ ∨ q.sat M ρ) ↔ (p.sat M σ ∨ q.sat M σ)
    constructor
    · intro hpq
      cases hpq with
      | inl hp => exact Or.inl ((ihp k ρ σ hs.1 h).mp hp)
      | inr hq => exact Or.inr ((ihq k ρ σ hs.2 h).mp hq)
    · intro hpq
      cases hpq with
      | inl hp => exact Or.inl ((ihp k ρ σ hs.1 h).mpr hp)
      | inr hq => exact Or.inr ((ihq k ρ σ hs.2 h).mpr hq)
  | impl p q ihp ihq =>
    change p.wellScoped k ∧ q.wellScoped k at hs
    change (p.sat M ρ → q.sat M ρ) ↔ (p.sat M σ → q.sat M σ)
    exact ⟨fun hpq hp => (ihq k ρ σ hs.2 h).mp (hpq ((ihp k ρ σ hs.1 h).mpr hp)),
      fun hpq hp => (ihq k ρ σ hs.2 h).mpr (hpq ((ihp k ρ σ hs.1 h).mp hp))⟩
  | all p ih =>
    change p.wellScoped (k + 1) at hs
    change (∀ a : A, p.sat M (push a ρ)) ↔ (∀ a : A, p.sat M (push a σ))
    exact ⟨fun hp a => (ih (k + 1) (push a ρ) (push a σ) hs
      (push_local k ρ σ h a)).mp (hp a),
      fun hp a => (ih (k + 1) (push a ρ) (push a σ) hs
      (push_local k ρ σ h a)).mpr (hp a)⟩
  | ex p ih =>
    change p.wellScoped (k + 1) at hs
    change (∃ a : A, p.sat M (push a ρ)) ↔ (∃ a : A, p.sat M (push a σ))
    constructor
    · intro hp
      obtain ⟨a, ha⟩ := hp
      exact ⟨a, (ih (k + 1) (push a ρ) (push a σ) hs (push_local k ρ σ h a)).mp ha⟩
    · intro hp
      obtain ⟨a, ha⟩ := hp
      exact ⟨a, (ih (k + 1) (push a ρ) (push a σ) hs (push_local k ρ σ h a)).mpr ha⟩

theorem sentence_assignment_independent (M : Model A) (p : Sentence)
    (ρ σ : Nat → A) : p.val.sat M ρ ↔ p.val.sat M σ :=
  sat_local M p.val 0 ρ σ p.property (fun i hi => False.elim (Nat.not_lt_zero i hi))

#print axioms push_local
#print axioms eval_local
#print axioms sat_local
#print axioms sentence_assignment_independent

end MathCan.ACE.Arithmetic
