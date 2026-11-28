import Init

/-!
# NOR-06: finite basin capture, tail permanence, and external ambiguity

This module is the Lean-checked discrete core of the next experiment:
an enclosure for a naturally sourced recurrent trajectory must enter
a previously proved invariant region before its contraction theorem
can apply. The analytic Jacobian, Banach, and Lp dimension reduction
arguments are cited separately in research/nor06.

The Boolean counterexample proves that knowing all transitions inside
a certified basin alone does not determine what happens outside it.
-/

namespace MathCan.BasinCapture

/-- Total iteration with the same order as the trained recurrent model:
apply the one-step transition n times. -/
def iterate {α : Type} (F : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => F (iterate F n x)

/-- Composition law for repeatedly applying a time-homogeneous map. -/
theorem iterate_add {α : Type} (F : α → α) (m n : Nat) (x : α) :
    iterate F (m + n) x = iterate F n (iterate F m x) := by
  induction n with
  | zero =>
    simp [iterate]
  | succ n ih =>
    rw [Nat.add_succ]
    simp only [iterate]
    exact congrArg F ih

/-- Any predicate invariant under one step remains true at all depths. -/
theorem invariant_from_inside {α : Type}
    (F : α → α) (B : α → Prop) (x : α)
    (hInv : ∀ y, B y → B (F y)) (hx : B x) :
    ∀ n, B (iterate F n x) := by
  intro n
  induction n with
  | zero => simpa [iterate] using hx
  | succ n ih =>
    simpa [iterate] using hInv (iterate F n x) ih

/-- A *finite* verified basin entry, with an invariant-basin theorem,
certifies all future time indices. -/
theorem capture_persists {α : Type}
    (F : α → α) (B : α → Prop) (x : α) (T : Nat)
    (hInv : ∀ y, B y → B (F y))
    (hEntry : B (iterate F T x)) :
    ∀ n, B (iterate F (T + n) x) := by
  intro n
  rw [iterate_add]
  exact invariant_from_inside F B (iterate F T x) hInv hEntry n

/-- A verified interval tube around an approximate state proves entry
as soon as its radius plus the center-to-target distance fits in R.
This is the arithmetic test passed to the all-depth Banach theorem. -/
theorem enclosure_enters_ball
    {α : Type} (d : α → α → Nat)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (actual approx center : α) (error offset R : Nat)
    (hApprox : d actual approx ≤ error)
    (hCenter : d approx center ≤ offset)
    (hClear : error + offset ≤ R) :
    d actual center ≤ R := by
  have ht := triangle actual approx center
  omega

/-- This is a precise obstruction to claiming basin entry from internal
contraction alone: both transitions agree inside the singleton basin
{false}, but their orbits from true behave differently. -/
def goodStep (_ : Bool) : Bool := false
def badStep (x : Bool) : Bool := x

theorem steps_agree_inside (x : Bool) (hx : x = false) :
    goodStep x = badStep x := by
  subst x
  rfl

theorem good_enters_from_outside : iterate goodStep 1 true = false := by
  rfl

theorem bad_never_enters_from_outside (n : Nat) :
    iterate badStep n true = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [iterate, badStep] using ih

#print axioms iterate_add
#print axioms invariant_from_inside
#print axioms capture_persists
#print axioms enclosure_enters_ball
#print axioms steps_agree_inside
#print axioms good_enters_from_outside
#print axioms bad_never_enters_from_outside

end MathCan.BasinCapture
