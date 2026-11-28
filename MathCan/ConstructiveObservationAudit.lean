import MathCan.ObservableQuotient
import MathCan.AuthorizationQuotient

/-!
# Constructive observation interfaces

The original existence theorems obtain a representative using classical
choice from surjectivity. Here an explicit section or a finite list of
representatives is supplied as executable data. The list need only cover
the image of the observation, not every possible observation. These
results keep the original abstract theorems and make their constructive
specialization usable by finite-state agent monitors.
-/

universe u v w

namespace MathCan.ConstructiveObservationAudit

open MathCan.ObservableQuotient
open MathCan.AuthorizationQuotient

/-- An explicit representative function suffices for factorization. -/
theorem factor_of_section {X : Type u} {Y : Type v}
    (obs : X → Y) (f : X → X) (sectionOf : Y → X)
    (rightInv : ∀ y, obs (sectionOf y) = y)
    (compatible : FiberCompatible obs f) :
    ∀ x, obs (f (sectionOf (obs x))) = obs (f x) :=
  fun x => compatible (sectionOf (obs x)) x (rightInv (obs x))

/-- The classifier can use a supplied representative function directly. -/
theorem authorization_of_section {S : Type u} {O : Type v} {A : Type w}
    (obs : S → O) (authorized : S → A → Bool) (sectionOf : O → S)
    (rightInv : ∀ o, obs (sectionOf o) = o)
    (compatible : AuthorizationFiberCompatible obs authorized) :
    ∀ s a, authorized (sectionOf (obs s)) a = authorized s a :=
  fun s a => compatible (sectionOf (obs s)) s (rightInv (obs s)) a

/-- Executable, deterministic first-match lookup. -/
def firstRepresentative {X : Type u} {Y : Type v} [DecidableEq Y]
    (obs : X → Y) (y : Y) : List X → Option X
  | [] => none
  | x :: xs => if obs x = y then some x else firstRepresentative obs y xs

/-- Every returned representative belongs to the supplied list and
    has the requested observation. -/
theorem lookup_sound {X : Type u} {Y : Type v} [DecidableEq Y]
    (obs : X → Y) (y : Y) (xs : List X) (r : X)
    (h : firstRepresentative obs y xs = some r) :
    r ∈ xs ∧ obs r = y := by
  induction xs with
  | nil => simp [firstRepresentative] at h
  | cons x tail ih =>
      by_cases hx : obs x = y
      · have he : x = r := by
          simpa [firstRepresentative, hx] using h
        subst r
        exact ⟨by simp, hx⟩
      · have ht : firstRepresentative obs y tail = some r := by
          simpa [firstRepresentative, hx] using h
        obtain ⟨hm, hy⟩ := ih ht
        exact ⟨List.mem_cons_of_mem x hm, hy⟩

/-- Existence in a finite supplied list is enough for lookup to succeed,
    using only the decidable equality procedure. -/
theorem lookup_complete {X : Type u} {Y : Type v} [DecidableEq Y]
    (obs : X → Y) (y : Y) (xs : List X)
    (h : ∃ r, r ∈ xs ∧ obs r = y) :
    ∃ r, firstRepresentative obs y xs = some r := by
  induction xs with
  | nil =>
      obtain ⟨r, hm, _⟩ := h
      simp at hm
  | cons x tail ih =>
      by_cases hx : obs x = y
      · exact ⟨x, by simp [firstRepresentative, hx]⟩
      · obtain ⟨r, hm, hy⟩ := h
        have ht : r ∈ tail := by
          rcases List.mem_cons.mp hm with he | he
          · subst r
            exact False.elim (hx hy)
          · exact he
        obtain ⟨q, hq⟩ := ih ⟨r, ht, hy⟩
        exact ⟨q, by simp [firstRepresentative, hx, hq]⟩

/-- A finite representative list need cover only observations of
    actual states. No total surjectivity or choice is assumed. -/
def CoversImage {X : Type u} {Y : Type v}
    (obs : X → Y) (xs : List X) : Prop :=
  ∀ x, ∃ r, r ∈ xs ∧ obs r = obs x

def finiteFactor {X : Type u} {Y : Type v} [DecidableEq Y]
    (obs : X → Y) (f : X → X) (xs : List X)
    (fallback : Y → Y) (y : Y) : Y :=
  match firstRepresentative obs y xs with
  | some x => obs (f x)
  | none => fallback y

theorem finite_factor_correct {X : Type u} {Y : Type v} [DecidableEq Y]
    (obs : X → Y) (f : X → X) (xs : List X) (fallback : Y → Y)
    (cover : CoversImage obs xs) (compatible : FiberCompatible obs f) :
    ∀ x, finiteFactor obs f xs fallback (obs x) = obs (f x) := by
  intro x
  obtain ⟨r, hr⟩ := lookup_complete obs (obs x) xs (cover x)
  have he := (lookup_sound obs (obs x) xs r hr).2
  simpa [finiteFactor, hr] using compatible r x he

/-- A finite authorization monitor fails closed for observations absent
    from the representative table. -/
def finiteAuthorization {S : Type u} {O : Type v} {A : Type w} [DecidableEq O]
    (obs : S → O) (authorized : S → A → Bool) (xs : List S)
    (o : O) (a : A) : Bool :=
  match firstRepresentative obs o xs with
  | some s => authorized s a
  | none => false

theorem finite_authorization_correct {S : Type u} {O : Type v} {A : Type w}
    [DecidableEq O] (obs : S → O) (authorized : S → A → Bool)
    (xs : List S) (cover : CoversImage obs xs)
    (compatible : AuthorizationFiberCompatible obs authorized) :
    ∀ s a, finiteAuthorization obs authorized xs (obs s) a = authorized s a := by
  intro s a
  obtain ⟨r, hr⟩ := lookup_complete obs (obs s) xs (cover s)
  have he := (lookup_sound obs (obs s) xs r hr).2
  simpa [finiteAuthorization, hr] using compatible r s he a

theorem finite_authorization_denies_unseen
    {S : Type u} {O : Type v} {A : Type w} [DecidableEq O]
    (obs : S → O) (authorized : S → A → Bool) (xs : List S)
    (o : O) (a : A) (missing : ∀ s, s ∈ xs → obs s ≠ o) :
    finiteAuthorization obs authorized xs o a = false := by
  cases h : firstRepresentative obs o xs with
  | none => simp [finiteAuthorization, h]
  | some r =>
      obtain ⟨hm, he⟩ := lookup_sound obs o xs r h
      exact False.elim (missing r hm he)

/-- A tiny executable monitor: hidden state is intentionally excluded
    from its decision; observation and action determine permission. -/
def demoObserve (s : Bool × Bool) : Nat := if s.1 then 1 else 0
def demoAuthorize (s : Bool × Bool) (a : Bool) : Bool := s.1 && a
def demoRepresentatives : List (Bool × Bool) := [(false, false), (true, false)]
def demoMonitor (o : Nat) (a : Bool) : Bool :=
  finiteAuthorization demoObserve demoAuthorize demoRepresentatives o a

theorem demo_monitor_correct (s : Bool × Bool) (a : Bool) :
    demoMonitor (demoObserve s) a = demoAuthorize s a := by
  rcases s with ⟨visible, hidden⟩
  cases visible <;> cases hidden <;> cases a <;> rfl

theorem demo_monitor_unknown_denied (a : Bool) :
    demoMonitor 2 a = false := by
  cases a <;> rfl

#print axioms factor_of_section
#print axioms authorization_of_section
#print axioms lookup_sound
#print axioms lookup_complete
#print axioms finite_factor_correct
#print axioms finite_authorization_correct
#print axioms finite_authorization_denies_unseen
#print axioms demo_monitor_correct
#print axioms demo_monitor_unknown_denied

end MathCan.ConstructiveObservationAudit
