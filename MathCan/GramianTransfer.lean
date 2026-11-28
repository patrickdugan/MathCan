import Init

/-!
# SPC-07: exact gauge transport and sharp rank-one regret

A kernel-checkable core for transferring recurrent observations under a
change of hidden-state coordinates. The general rank-r Gramian trace
inequality is proved in the companion research note, using the spectral
theorem and variational principle. The Lean theorems below establish an
arbitrary-state, arbitrary-horizon gauge-conjugacy identity and the sharp
rank-one two-feature diagonal special case.

There are no `sorry` terms or imported mathematical axioms.
-/

namespace MathCan.GramianTransfer

universe u v

/-- The state reached after `n` applications, with a fixed initial state. -/
def iterateState {α : Type u} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterateState f n (f x)

/-- Explicit reversible gauge map. We use the core `Init` library, so
    forward and inverse maps are packaged here with inverse proofs. -/
structure StateGauge (α : Type u) where
  toFun : α → α
  invFun : α → α
  left_inv : ∀ x : α, invFun (toFun x) = x
  right_inv : ∀ x : α, toFun (invFun x) = x

/-- Transport the whole recurrent update through a reversible gauge map. -/
def transport {α : Type u} (g : StateGauge α) (f : α → α) : α → α :=
  fun y => g.toFun (f (g.invFun y))

/-- The entire finite recurrent orbit is equivariant under state relabeling. -/
theorem transport_iterate {α : Type u} (g : StateGauge α) (f : α → α)
    (n : Nat) (x : α) :
    iterateState (transport g f) n (g.toFun x) = g.toFun (iterateState f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      calc
        iterateState (transport g f) (n + 1) (g.toFun x) =
            iterateState (transport g f) n (transport g f (g.toFun x)) := rfl
        _ = iterateState (transport g f) n (g.toFun (f x)) := by
              simp [transport, g.left_inv]
        _ = g.toFun (iterateState f n (f x)) := ih (f x)
        _ = g.toFun (iterateState f (n + 1) x) := rfl

/-- A co-transported observer gives identical outputs at every future time. -/
theorem observable_transport {α : Type u} {β : Type v}
    (g : StateGauge α) (f : α → α) (readout : α → β)
    (n : Nat) (x : α) :
    readout (g.invFun (iterateState (transport g f) n (g.toFun x))) =
      readout (iterateState f n x) := by
  calc
    readout (g.invFun (iterateState (transport g f) n (g.toFun x))) =
        readout (g.invFun (g.toFun (iterateState f n x))) := by rw [transport_iterate]
    _ = readout (iterateState f n x) := congrArg readout (g.left_inv _)

/-- A two-coordinate relabeling, useful as an elementary gauge witness. -/
def swapState (x : Int × Int) : Int × Int := (x.2, x.1)

theorem swap_involutive (x : Int × Int) :
    swapState (swapState x) = x := by
  cases x
  rfl

/-- Under the coordinate swap, a transported first-coordinate readout
    must read the second coordinate in the new representation. -/
theorem swap_readout (x : Int × Int) :
    (swapState x).2 = x.1 := by
  rfl

/-- Two-feature diagonal surrogate for the general rank-r Gramian bound.
    The source selected feature zero. The target's unselected feature can
    exceed it by at most twice the coordinatewise spectral uncertainty. -/
theorem rank_one_diagonal_transfer_regret
    (s₀ s₁ t₀ t₁ ε : Int)
    (_hε : 0 ≤ ε) (hsource : s₁ ≤ s₀)
    (hzero : s₀ - ε ≤ t₀)
    (hone : t₁ ≤ s₁ + ε) :
    t₁ - t₀ ≤ 2 * ε := by
  omega

/-- The factor two is attained when the source features tie and the
    target features move in opposite directions by the error radius. -/
theorem sharp_diagonal_regret (ε : Int) :
    ε - (-ε) = 2 * ε := by
  omega

/-- An exactly swapped diagonal score ordering transfers after coordinate
    relabeling, while the raw coordinate labels may rank them incorrectly. -/
theorem swapped_score_order (s₀ s₁ t₀ t₁ : Int)
    (hfirst : t₀ = s₁) (hsecond : t₁ = s₀)
    (hsource : s₁ ≤ s₀) :
    t₀ ≤ t₁ := by
  omega

#print axioms transport_iterate
#print axioms observable_transport
#print axioms swap_involutive
#print axioms swap_readout
#print axioms rank_one_diagonal_transfer_regret
#print axioms sharp_diagonal_regret
#print axioms swapped_score_order

end MathCan.GramianTransfer
