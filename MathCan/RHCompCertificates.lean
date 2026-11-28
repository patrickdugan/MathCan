import Lean

/-!
RH-COMP-08..12: certificate foundations.
Arithmetic uses Int savings to avoid truncated subtraction.
Future equivalence is defined over every finite action word; no dimension
or GF(2) rank theorem is claimed here. The finite linear rank/cardinality
bridge and latest-end interval exchange remain separate obligations.
-/
namespace MathCan.RHCompCertificates

def rootSaving (u b c : Int) : Int := u * (b - c)
def closureSaving (u b c h : Int) : Int := (u - 1) * b - u * c - h

theorem FactoringClosureMonotonicity (b c h : Int) (pos : 0 < c + h) :
    closureSaving 1 b c h < 0 := by
  simp [closureSaving]
  omega

theorem singleUseClosureIdentity (b c h : Int) :
    closureSaving 1 b c h = -(c + h) := by
  simp [closureSaving]
  omega

theorem rootShrinkClosureGrowth (b c h : Int) (shrink : c < b)
    (pos : 0 < c + h) :
    0 < rootSaving 1 b c ∧ closureSaving 1 b c h < 0 := by
  constructor
  · simp [rootSaving]
    omega
  · exact FactoringClosureMonotonicity b c h pos

/-- A lower bound matched by a feasible witness certifies a minimum. -/
theorem minCertificate {X : Type} (valid : X → Prop) (cost : X → Nat)
    (w : X) (B : Nat) (hw : valid w) (lower : ∀ x, valid x → B ≤ cost x)
    (matchBound : cost w = B) :
    valid w ∧ ∀ x, valid x → cost w ≤ cost x := by
  refine ⟨hw, ?_⟩
  intro x hx
  rw [matchBound]
  exact lower x hx

/-- Joint optimality is equivalent to joint feasibility at independently
    certified optima. Path/replay realizability is supplied by valid. -/
theorem SinkConventionInvariance {X : Type} (valid : X → Prop)
    (release retain : X → Nat) (p q : Nat)
    (lo₀ : ∀ x, valid x → p ≤ release x)
    (lo₁ : ∀ x, valid x → q ≤ retain x) :
    (∃ x, valid x ∧ release x ≤ p ∧ retain x ≤ q) ↔
    (∃ x, valid x ∧ release x = p ∧ retain x = q) := by
  constructor
  · rintro ⟨x, hx, h₀, h₁⟩
    exact ⟨x, hx, Nat.le_antisymm h₀ (lo₀ x hx),
      Nat.le_antisymm h₁ (lo₁ x hx)⟩
  · rintro ⟨x, hx, h₀, h₁⟩
    exact ⟨x, hx, Nat.le_of_eq h₀, Nat.le_of_eq h₁⟩

def runWord {X A : Type} (step : A → X → X) : List A → X → X
  | [], x => x
  | a :: w, x => runWord step w (step a x)

def FutureEq {X A Y : Type} (step : A → X → X) (obs : X → Y)
    (x y : X) : Prop :=
  ∀ w, obs (runWord step w x) = obs (runWord step w y)

theorem futureEq_observation {X A Y : Type} (step : A → X → X)
    (obs : X → Y) (x y : X) (h : FutureEq step obs x y) :
    obs x = obs y := h []

theorem futureEq_step {X A Y : Type} (step : A → X → X)
    (obs : X → Y) (x y : X) (a : A) (h : FutureEq step obs x y) :
    FutureEq step obs (step a x) (step a y) := by
  intro w
  exact h (a :: w)

/-- Every observation-respecting action congruence refines FutureEq. -/
theorem futureEq_coarsest {X A Y : Type} (step : A → X → X)
    (obs : X → Y) (R : X → X → Prop)
    (observe : ∀ x y, R x y → obs x = obs y)
    (preserve : ∀ a x y, R x y → R (step a x) (step a y))
    (x y : X) (h : R x y) : FutureEq step obs x y := by
  intro w
  induction w generalizing x y with
  | nil => exact observe x y h
  | cons a w ih => exact ih (step a x) (step a y) (preserve a x y h)

/-- Arithmetic part of an interval dual witness: assign selected intervals
    to covered time points or their own uncovered slot, then sum capacities.
    The charge conservation and capacity bounds must be proved separately. -/
theorem IntervalDualWeakBound (selected covered uncovered cap z : Nat)
    (partition : selected = covered + uncovered)
    (capacityBound : covered ≤ cap) (uncoveredBound : uncovered ≤ z) :
    selected ≤ cap + z := by omega

/-- Finite chain bound under explicit strict rank growth prior to closure.
    The linear subspace strictness and rank-nullity proofs are separate. -/
theorem stabilizationHorizonBound (d r h : Nat) (growth : r + h ≤ d) :
    h ≤ d - r := by omega

#print axioms FactoringClosureMonotonicity
#print axioms SinkConventionInvariance
#print axioms futureEq_coarsest
#print axioms IntervalDualWeakBound
end MathCan.RHCompCertificates
