import MathCan.GraphWitness

/-!
SWC-01C: exact local F3 witnesses under a pinned graph anchor.

The positive rook assignment witnesses local consistency of edge equality
constraints with pins at vertices 1 and 4, for anchor vertex 0.
For Shrikhande, the two graph edges 1--5 and 5--4 force equality of the
pinned variables, making the same pins inconsistent.

The full per-anchor F3 rank and pin-pair counts are handled by independent
mod-three Gaussian elimination in the Control-Harness finite reference.
-/
namespace MathCan.GraphWitnessF3

/-- A concrete F3 assignment for the six rook neighbors of vertex zero.
The row neighbors have value 0 and column neighbors value 1. -/
def rookLocalAssignment (u : Fin 16) : Fin 3 :=
  if u.val % 4 == 0 then 1 else 0

theorem rook_local_pinned_values :
    rookLocalAssignment 1 = 0 ∧ rookLocalAssignment 4 = 1 := by
  decide

theorem rook_local_edge_equalities :
    ∀ u v : Fin 16,
      MathCan.GraphWitness.rookEdge 0 u = true →
      MathCan.GraphWitness.rookEdge 0 v = true →
      MathCan.GraphWitness.rookEdge u v = true →
      rookLocalAssignment u = rookLocalAssignment v := by
  decide

/-- Both paths are inside the six-vertex neighborhood of Shrikhande's
zero anchor, and 1--5--4 connects the chosen pinned vertices. -/
theorem shrikhande_local_obstruction_edges :
    MathCan.GraphWitness.shrikhandeEdge 0 1 = true ∧
    MathCan.GraphWitness.shrikhandeEdge 0 5 = true ∧
    MathCan.GraphWitness.shrikhandeEdge 0 4 = true ∧
    MathCan.GraphWitness.shrikhandeEdge 1 5 = true ∧
    MathCan.GraphWitness.shrikhandeEdge 5 4 = true := by
  decide

/-- The two F3 pins x1=0,x4=1 cannot coexist with edge equalities
x1=x5 and x5=x4. This argument holds in any type with 0≠1. -/
theorem shrikhande_two_pins_inconsistent
    (x : Fin 16 → Fin 3)
    (h15 : x 1 = x 5)
    (h54 : x 5 = x 4)
    (h1 : x 1 = 0)
    (h4 : x 4 = 1) : False := by
  have h01 : (0 : Fin 3) = 1 := by
    calc
      (0 : Fin 3) = x 1 := h1.symm
      _ = x 5 := h15
      _ = x 4 := h54
      _ = 1 := h4
  exact (by decide : (0 : Fin 3) ≠ 1) h01

#print axioms rook_local_pinned_values
#print axioms rook_local_edge_equalities
#print axioms shrikhande_local_obstruction_edges
#print axioms shrikhande_two_pins_inconsistent

end MathCan.GraphWitnessF3
