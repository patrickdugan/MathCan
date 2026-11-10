import Init

/-!
# Exact path holonomy and gauge invariance for additive edge quotes

This is the algebraic, kernel-checked part of CHTR-02. A path is a starting
vertex followed by a list of visited vertices. In particular, the theorem
works for repeated vertices, directed edges and arbitrary finite walks.

The rational weighted cycle-Gram identity and robust uncertainty estimates
have paper proofs and `Fraction` oracles in `research/chitraverse`;
those statements are not yet formalized in Lean.
-/

namespace MathCan.Hodge

universe u

/-- Add edge quotes along a directed walk, starting at `start`. -/
def pathSum {V : Type u} (q : V → V → Int) (start : V) : List V → Int
  | [] => 0
  | next :: rest => q start next + pathSum q next rest

/-- Endpoint after following a finite walk. -/
def endpoint {V : Type u} (start : V) : List V → V
  | [] => start
  | next :: rest => endpoint next rest

/-- Endpoint of a walk with a concatenated suffix. -/
theorem endpoint_append {V : Type u} (start : V) (xs ys : List V) :
    endpoint start (xs ++ ys) = endpoint (endpoint start xs) ys := by
  induction xs generalizing start with
  | nil => simp [endpoint]
  | cons next xs ih =>
      simp [endpoint, ih]

/-- The line integral along a concatenated walk is additive. -/
theorem pathSum_append {V : Type u} (q : V → V → Int)
    (start : V) (xs ys : List V) :
    pathSum q start (xs ++ ys) =
      pathSum q start xs + pathSum q (endpoint start xs) ys := by
  induction xs generalizing start with
  | nil => simp [pathSum, endpoint]
  | cons next xs ih =>
      simp [pathSum, endpoint, ih, Int.add_assoc]

/-- Adding a vertex potential shifts a path quote by the endpoint difference. -/
theorem pathSum_gauge {V : Type u} (q : V → V → Int)
    (p : V → Int) (start : V) (xs : List V) :
    pathSum (fun u v => q u v + (p v - p u)) start xs =
      pathSum q start xs + (p (endpoint start xs) - p start) := by
  induction xs generalizing start with
  | nil => simp [pathSum, endpoint]
  | cons next xs ih =>
      simp only [pathSum, endpoint]
      rw [ih next]
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Closed-walk holonomy is exactly invariant under all vertex gauges. -/
theorem closed_path_gauge {V : Type u} (q : V → V → Int)
    (p : V → Int) (start : V) (xs : List V)
    (closed : endpoint start xs = start) :
    pathSum (fun u v => q u v + (p v - p u)) start xs =
      pathSum q start xs := by
  rw [pathSum_gauge, closed]
  simp

/-- Zero edge quotes integrate to zero along every finite walk. -/
theorem pathSum_zero {V : Type u} (start : V) (xs : List V) :
    pathSum (fun _ _ => (0 : Int)) start xs = 0 := by
  induction xs generalizing start with
  | nil => rfl
  | cons next xs ih =>
      simp [pathSum, ih next]

/-- A pure potential difference has zero circulation on a closed walk. -/
theorem closed_potential_zero {V : Type u}
    (p : V → Int) (start : V) (xs : List V)
    (closed : endpoint start xs = start) :
    pathSum (fun u v => p v - p u) start xs = 0 := by
  have h := closed_path_gauge (fun _ _ => (0 : Int)) p start xs closed
  simpa [pathSum_zero] using h

/-- Each individual squared residual input is unchanged by a simultaneous gauge. -/
theorem edge_residual_gauge (q pu pv xu xv : Int) :
    (q + (pv - pu)) - ((xv + pv) - (xu + pu)) =
      q - (xv - xu) := by
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

#print axioms endpoint_append
#print axioms pathSum_append
#print axioms pathSum_gauge
#print axioms closed_path_gauge
#print axioms pathSum_zero
#print axioms closed_potential_zero
#print axioms edge_residual_gauge

end MathCan.Hodge