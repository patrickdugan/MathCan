import Init

/-!
# TOE-01 finite graph gauge identities

These kernel lemmas formalize additive graph holonomy. The companion note
contains the Gaussian KL and Friedmann polynomial arguments, which have
rational executable tests and are not yet formalized in Lean.
-/
namespace MathCan.TOEGraph

abbrev Edge := Nat × Nat

def gradient (p : Nat → Int) (edge : Edge) : Int :=
  p edge.2 - p edge.1

def integral (f : Edge → Int) : List Edge → Int
  | [] => 0
  | e :: es => f e + integral f es

def chain (start : Nat) : List Edge → Prop
  | [] => True
  | e :: es => e.1 = start ∧ chain e.2 es

def endpoint (start : Nat) : List Edge → Nat
  | [] => start
  | e :: es => endpoint e.2 es

theorem integral_add (f g : Edge → Int) (es : List Edge) :
    integral (fun e => f e + g e) es = integral f es + integral g es := by
  induction es with
  | nil => simp [integral]
  | cons e rest ih =>
      simp only [integral]
      rw [ih]
      omega

theorem integral_ext (f g : Edge → Int) (es : List Edge)
    (h : ∀ e, f e = g e) : integral f es = integral g es := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
      simp only [integral]
      rw [h e, ih]

theorem integral_gradient (p : Nat → Int) (start : Nat)
    (es : List Edge) (valid : chain start es) :
    integral (gradient p) es = p (endpoint start es) - p start := by
  induction es generalizing start with
  | nil => simp [integral, endpoint]
  | cons e rest ih =>
      rcases e with ⟨u,v⟩
      simp only [chain] at valid
      rcases valid with ⟨hstart,hrest⟩
      subst u
      simp only [integral, endpoint, gradient]
      rw [ih v hrest]
      omega

theorem closed_gradient_zero (p : Nat → Int) (start : Nat)
    (es : List Edge) (valid : chain start es)
    (closed : endpoint start es = start) :
    integral (gradient p) es = 0 := by
  rw [integral_gradient p start es valid, closed]
  omega

theorem closed_gauge_invariant (f : Edge → Int) (p : Nat → Int)
    (start : Nat) (es : List Edge) (valid : chain start es)
    (closed : endpoint start es = start) :
    integral (fun e => f e + gradient p e) es = integral f es := by
  rw [integral_add, closed_gradient_zero p start es valid closed]
  omega

theorem nonzero_cycle_obstructs_potential (f : Edge → Int)
    (start : Nat) (es : List Edge) (valid : chain start es)
    (closed : endpoint start es = start)
    (nonzero : integral f es ≠ 0) :
    ¬ ∃ p : Nat → Int, ∀ e, f e = gradient p e := by
  intro witness
  rcases witness with ⟨p, h⟩
  have hEq := integral_ext f (gradient p) es h
  have hZero := closed_gradient_zero p start es valid closed
  omega

#print axioms integral_add
#print axioms integral_ext
#print axioms integral_gradient
#print axioms closed_gradient_zero
#print axioms closed_gauge_invariant
#print axioms nonzero_cycle_obstructs_potential

end MathCan.TOEGraph
