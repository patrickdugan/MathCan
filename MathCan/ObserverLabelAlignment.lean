import Init

/-!
COE-09: finite, axiom-auditable certificates for evaluator-code alignment.

A complete graph can be perfectly separated by codes even while every
held-out target is decoded incorrectly following a derangement of labels.
The general permutation theorem and dark-fiber rotation identity are proved
in the companion manuscript. This Init-only module checks a complete finite
counterexample and abstract readout preservation, without an axiom for an
unverified pretrained-model result.
-/
namespace MathCan.ObserverLabelAlignment

set_option maxHeartbeats 1000000

/-- Three distinct codewords representing an abstract complete K3 evaluator. -/
def binaryCode3 (i : Fin 3) : Nat := i.val

/-- A cyclic derangement of the three target labels. -/
def shiftedTarget3 (i : Fin 3) : Nat := (i.val + 1) % 3

/-- Every evaluator edge remains separated by a three-code assignment. -/
theorem k3_complete_edge_separation :
    ∀ u v : Fin 3, u ≠ v → binaryCode3 u ≠ binaryCode3 v := by
  decide

/-- Despite perfect separation, decoding the code as its fit label is wrong
    on all three held-out points with a cyclic label correspondence. -/
theorem k3_total_label_failure :
    ∀ u : Fin 3, binaryCode3 u ≠ shiftedTarget3 u := by
  decide

/-- Reordering the codes of K3 retains three distinct unordered code pairs. -/
def k3SeparationCount (a b c : Nat) : Nat :=
    (if a = b then 0 else 1) +
    (if a = c then 0 else 1) +
    (if b = c then 0 else 1)

theorem k3_collision_count_rotates (a b c : Nat) :
    k3SeparationCount a b c = k3SeparationCount b c a := by
  simp [k3SeparationCount, eq_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- A dark-sector transformation of a product state preserves the visible
    coordinate of every input, independent of the dark update function. -/
def changeDark {α β : Type} (g : β → β) (state : α × β) : α × β :=
    (state.1, g state.2)

theorem changeDark_visible_invariance {α β : Type} (g : β → β) (s : α × β) :
    (changeDark g s).1 = s.1 := by
  rfl

/-- If an intervention preserves the dark-component squared norm, then the
    total squared norm, expressed as orthogonal-sum accounting, is unchanged. -/
theorem orthogonal_norm_budget
    (visibleSq originalDarkSq newDarkSq : Nat)
    (h : originalDarkSq = newDarkSq) :
    visibleSq + originalDarkSq = visibleSq + newDarkSq := by
  omega

#print axioms k3_complete_edge_separation
#print axioms k3_total_label_failure
#print axioms k3_collision_count_rotates
#print axioms changeDark_visible_invariance
#print axioms orthogonal_norm_budget

end MathCan.ObserverLabelAlignment
