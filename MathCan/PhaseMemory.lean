import Init

/-!
SPC-04: exact finite algebra for phase-memory separation.

Lean checks the two-node superattracting polynomial specialization,
a nilpotent alternating-Jacobian counterexample, and finite phase
injection. The general real Hermite interpolation theorem and numerical
Floquet claims remain in research/spectral_aliasing/SPC-04.md.
-/
namespace MathCan.PhaseMemory

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A two-cycle of the Hermite interpolation construction. -/
def togglePoly (x : Int) : Int := 1 - 3 * x * x + 2 * x * x * x

def toggleFormalDerivative (x : Int) : Int := -6 * x + 6 * x * x

theorem toggle_zero_to_one : togglePoly 0 = 1 := by decide
theorem toggle_one_to_zero : togglePoly 1 = 0 := by decide
theorem derivative_zero_at_zero : toggleFormalDerivative 0 = 0 := by decide
theorem derivative_zero_at_one : toggleFormalDerivative 1 = 0 := by decide

theorem two_step_orbit_exact :
    togglePoly (togglePoly 0) = 0 ∧ togglePoly (togglePoly 1) = 1 := by
  decide

/-- Concrete 2 x 2 matrices, with the multiplication order explicit. -/
def upperTwo (i j : Fin 2) : Int :=
  if i.val == 0 && j.val == 1 then 2 else 0

def lowerTwo (i j : Fin 2) : Int :=
  if i.val == 1 && j.val == 0 then 2 else 0

def matMul (a b : Fin 2 → Fin 2 → Int) (i j : Fin 2) : Int :=
  a i 0 * b 0 j + a i 1 * b 1 j

/-- Both one-step matrices are nilpotent, with square zero. -/
theorem upper_nilpotent :
    ∀ i j : Fin 2, matMul upperTwo upperTwo i j = 0 := by decide

theorem lower_nilpotent :
    ∀ i j : Fin 2, matMul lowerTwo lowerTwo i j = 0 := by decide

/-- The two-step product has a factor four on the second coordinate. -/
theorem alternating_product_grows :
    matMul lowerTwo upperTwo 0 0 = 0 ∧
    matMul lowerTwo upperTwo 0 1 = 0 ∧
    matMul lowerTwo upperTwo 1 0 = 0 ∧
    matMul lowerTwo upperTwo 1 1 = 4 := by
  decide

/-- A complete readout distinguishes its internal phase states. -/
theorem exact_phase_readout_requires_injective_memory
    {Phase Memory Output : Type}
    (state : Phase → Memory) (readout : Memory → Output)
    (h : Function.Injective (fun p => readout (state p))) :
    Function.Injective state := by
  intro a b hab
  exact h (congrArg readout hab)

/-- The finite Boolean phase flip generates an exact period-two orbit. -/
def flipBits {m : Nat} (a : Fin m → Bool) : Fin m → Bool :=
  fun i => !(a i)

theorem flip_twice {m : Nat} (a : Fin m → Bool) :
    flipBits (flipBits a) = a := by
  funext i
  cases h : a i <;> simp [flipBits, h]

#print axioms toggle_zero_to_one
#print axioms toggle_one_to_zero
#print axioms derivative_zero_at_zero
#print axioms derivative_zero_at_one
#print axioms two_step_orbit_exact
#print axioms upper_nilpotent
#print axioms lower_nilpotent
#print axioms alternating_product_grows
#print axioms exact_phase_readout_requires_injective_memory
#print axioms flip_twice
end MathCan.PhaseMemory
