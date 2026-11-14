import Init

/-!
SWC-01: finite rook/Shrikhande symmetry and witness certificates.

Source families: OpenAI Math #133 (Weisfeiler–Leman refinement) and
#243 (choiceless counting and witnessed symmetric choice).

This Init-only module kernel-checks the finite 16-vertex graph data,
common-neighbor counts, local triangle witnesses, and an explicit
four-clique. The full general 2-WL refinement argument and the
choice-logic separation are paper-level mathematics with separate
Python finite refinement checks. Neither source theorem is claimed
formalized by this file.
-/

namespace MathCan.GraphWitness

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

def rookEdge (u v : Fin 16) : Bool :=
  if u == v then false else
  (u.val / 4 == v.val / 4) || (u.val % 4 == v.val % 4)

/-- Differences modulo four for the 4×4 Shrikhande Cayley graph. -/
def difference (a b : Nat) : Nat := (b + 4 - a) % 4

def shrikhandeEdge (u v : Fin 16) : Bool :=
  if u == v then false else
  let x := difference (u.val / 4) (v.val / 4)
  let y := difference (u.val % 4) (v.val % 4)
  (x == 1 && y == 0) ||
  (x == 3 && y == 0) ||
  (x == 0 && y == 1) ||
  (x == 0 && y == 3) ||
  (x == 1 && y == 1) ||
  (x == 3 && y == 3)

def neighborhood (e : Fin 16 → Fin 16 → Bool) (u : Fin 16) :
    List (Fin 16) :=
  (List.finRange 16).filter (fun v => e u v)

def commonCount (e : Fin 16 → Fin 16 → Bool)
    (u v : Fin 16) : Nat :=
  ((List.finRange 16).filter (fun w => e u w && e v w)).length

/-- Four-cliques through an anchor correspond exactly to triangles
in the induced six-vertex neighborhood. Every triangle is counted
once because its vertices are ordered increasingly. -/
def anchoredFourCliques (e : Fin 16 → Fin 16 → Bool)
    (u : Fin 16) : Nat :=
  let ns := neighborhood e u
  (ns.flatMap (fun a =>
    ns.flatMap (fun b =>
      ns.filter (fun c =>
        decide (a.val < b.val) &&
        decide (b.val < c.val) &&
        e a b && e a c && e b c)))).length

/-- Six neighbors around each vertex in both examples. -/
theorem rook_degree_six :
    ∀ u : Fin 16, (neighborhood rookEdge u).length = 6 := by
  decide

theorem shrikhande_degree_six :
    ∀ u : Fin 16, (neighborhood shrikhandeEdge u).length = 6 := by
  decide

/-- Any two distinct vertices have two common neighbors.
These are the (16,6,2,2) parameters for this specific pair. -/
theorem rook_common_two :
    ∀ u v : Fin 16, u ≠ v → commonCount rookEdge u v = 2 := by
  decide

theorem shrikhande_common_two :
    ∀ u v : Fin 16, u ≠ v → commonCount shrikhandeEdge u v = 2 := by
  decide

/-- Rooted local witness count separates the graphs at EVERY anchor. -/
theorem rook_two_anchored_four_cliques :
    ∀ u : Fin 16, anchoredFourCliques rookEdge u = 2 := by
  decide

theorem shrikhande_zero_anchored_four_cliques :
    ∀ u : Fin 16, anchoredFourCliques shrikhandeEdge u = 0 := by
  decide

/-- Explicit positive witness: the four vertices of row zero. -/
theorem rook_first_row_clique :
    rookEdge 0 1 && rookEdge 0 2 && rookEdge 0 3 &&
    rookEdge 1 2 && rookEdge 1 3 && rookEdge 2 3 = true := by
  decide

/-- Each K4 is counted at its four vertices, so total anchored
counts are 32 for rook and 0 for Shrikhande. -/
theorem rook_total_anchored_four_cliques :
    ((List.finRange 16).map (anchoredFourCliques rookEdge)).sum = 32 := by
  decide

theorem shrikhande_total_anchored_four_cliques :
    ((List.finRange 16).map (anchoredFourCliques shrikhandeEdge)).sum = 0 := by
  decide

#print axioms rook_degree_six
#print axioms shrikhande_degree_six
#print axioms rook_common_two
#print axioms shrikhande_common_two
#print axioms rook_two_anchored_four_cliques
#print axioms shrikhande_zero_anchored_four_cliques
#print axioms rook_first_row_clique
#print axioms rook_total_anchored_four_cliques
#print axioms shrikhande_total_anchored_four_cliques

end MathCan.GraphWitness
