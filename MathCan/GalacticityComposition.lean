import Lean

namespace GalacticityComposition

/-- If both components pay for themselves by m, their additive composition
    pays for itself by m. -/
theorem additive_upper (C₁ C₂ d₁ d₂ m : Nat)
    (h₁ : C₁ ≤ m * d₁) (h₂ : C₂ ≤ m * d₂) :
    C₁ + C₂ ≤ m * (d₁ + d₂) := by
  rw [Nat.mul_add]
  omega

theorem additive_lower (C₁ C₂ d₁ d₂ m : Nat)
    (h₁ : m * d₁ ≤ C₁) (h₂ : m * d₂ ≤ C₂) :
    m * (d₁ + d₂) ≤ C₁ + C₂ := by
  rw [Nat.mul_add]
  omega

/-- Positive weighted average lies between common lower and upper bounds,
    stated without division or rounding. -/
theorem additive_sandwich (C₁ C₂ d₁ d₂ lo hi : Nat)
    (h₁ : lo * d₁ ≤ C₁) (h₂ : lo * d₂ ≤ C₂)
    (h₃ : C₁ ≤ hi * d₁) (h₄ : C₂ ≤ hi * d₂) :
    lo * (d₁ + d₂) ≤ C₁ + C₂ ∧ C₁ + C₂ ≤ hi * (d₁ + d₂) :=
  ⟨additive_lower C₁ C₂ d₁ d₂ lo h₁ h₂,
   additive_upper C₁ C₂ d₁ d₂ hi h₃ h₄⟩

/-- Finite deterministic adaptive bit-probe tree for one response. The input
    can encode all slices and queries preceding the response. -/
inductive ProbeTree (Q : Type) where
  | leaf : Bool → ProbeTree Q
  | ask : Q → ProbeTree Q → ProbeTree Q → ProbeTree Q

def ProbeTree.run {Q : Type} (o : Q → Bool) : ProbeTree Q → Bool
  | .leaf b => b
  | .ask q l r => if o q then run o r else run o l

def ProbeTree.path {Q : Type} (o : Q → Bool) : ProbeTree Q → List Q
  | .leaf _ => []
  | .ask q l r => q :: (if o q then path o r else path o l)

/-- Only the actual transcript matters. The alternative oracle need not
    agree on any unvisited query. -/
theorem same_path_run {Q : Type} (o o' : Q → Bool) (tree : ProbeTree Q)
    (h : ∀ q, q ∈ tree.path o → o' q = o q) :
    tree.run o' = tree.run o := by
  induction tree with
  | leaf b => rfl
  | ask q l r ihl ihr =>
    have hq : o' q = o q := h q (by simp [ProbeTree.path])
    cases e : o q with
    | false =>
      have hl : ∀ a, a ∈ l.path o → o' a = o a := by
        intro a ha
        apply h a
        simp [ProbeTree.path, e, ha]
      simp [ProbeTree.run, hq, e, ihl hl]
    | true =>
      have hr : ∀ a, a ∈ r.path o → o' a = o a := by
        intro a ha
        apply h a
        simp [ProbeTree.path, e, ha]
      simp [ProbeTree.run, hq, e, ihr hr]

/-- Any exact adaptive implementation must separate worlds with different
    target values somewhere on its observed path. -/
theorem exact_requires_separation {Q W : Type} (oracle : W → Q → Bool)
    (target : W → Bool) (tree : ProbeTree Q)
    (correct : ∀ w, tree.run (oracle w) = target w)
    (x y : W) (h : ∀ q, q ∈ tree.path (oracle x) →
      oracle y q = oracle x q) : target x = target y := by
  rw [← correct x, ← correct y]
  exact (same_path_run (oracle x) (oracle y) tree h).symm

theorem indistinguishability_obstruction {Q W : Type} (oracle : W → Q → Bool)
    (target : W → Bool) (tree : ProbeTree Q)
    (x y : W) (different : target x ≠ target y)
    (h : ∀ q, q ∈ tree.path (oracle x) → oracle y q = oracle x q) :
    ¬ ∀ w, tree.run (oracle w) = target w := by
  intro correct
  exact different (exact_requires_separation oracle target tree correct x y h)

end GalacticityComposition
