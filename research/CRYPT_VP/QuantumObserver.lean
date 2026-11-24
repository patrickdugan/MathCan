import ObserverBound
import Mathlib.Data.Complex.Basic

/-! QOBS-01: Hilbert-Schmidt energy by real coordinate flattening.
    J may be the pair of matrix row and column indices. No positivity,
    trace or purity assumption is needed for this inequality. -/
open scoped BigOperators
open Finset
namespace VPVNP.Binary
noncomputable section
attribute [local instance] unitMatrixFintype rankOneFintype

def complexCoords {J : Type*} (z : J → ℂ) (p : J × Bool) : ℝ :=
  if p.2 then (z p.1).im else (z p.1).re

def hsShiftSq {J : Type*} [Fintype J] (z w : J → ℂ) : ℝ :=
  ∑ p : J × Bool, (if p.2 then (z p.1 - w p.1).im else
    (z p.1 - w p.1).re)^2

theorem hs_shift_coords {J : Type*} [Fintype J] (z w : J → ℂ) :
    hsShiftSq z w = ∑ p : J × Bool, (complexCoords z p - complexCoords w p)^2 := by
  unfold hsShiftSq
  apply Finset.sum_congr rfl
  intro p hp
  rcases p with ⟨j, q⟩
  cases q <;> simp [complexCoords, Complex.sub_re, Complex.sub_im]

def hsEnergy {I T J : Type*} [Fintype I] [DecidableEq I] [Fintype T] [Fintype J]
    (inc : T → Bits I) (f : Bits I → J → ℂ) : ℝ :=
  (∑ t : T, ∑ a : Bits I, hsShiftSq (f (a + inc t)) (f a)) /
    ((Fintype.card (Bits I) : ℝ) * (Fintype.card T : ℝ))

theorem hs_energy_coords {I T J : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    [Fintype J] (inc : T → Bits I) (f : Bits I → J → ℂ) :
    hsEnergy inc f = vectorEnergy inc (fun a => complexCoords (f a)) := by
  rw [vector_energy_mean]
  unfold hsEnergy
  simp_rw [hs_shift_coords]

theorem hs_sharp_bound {J : Type*} [Fintype J] (n : ℕ) (hn : 0 < n)
    (f : MatrixBits n → J → ℂ) :
    hsEnergy (fullIncrement n) f ≤ sharpConstant n * hsEnergy (oneIncrement n) f := by
  rw [hs_energy_coords, hs_energy_coords]
  exact sharp_observer_bound n hn (fun a => complexCoords (f a))

theorem hs_sharp_defect {J : Type*} [Fintype J] (n : ℕ) (hn : 0 < n)
    (f : MatrixBits n → J → ℂ) :
    hsEnergy (fullIncrement n) f +
      sharpConstant n / 3 * highRankEnergy n (fun a => complexCoords (f a)) ≤
        sharpConstant n * hsEnergy (oneIncrement n) f := by
  rw [hs_energy_coords, hs_energy_coords]
  exact sharp_observer_defect n hn (fun a => complexCoords (f a))

/-- The (i,j) entry of a real phase outer product has frequency B_i+B_j.
    For complex amplitudes the same real Walsh sign multiplies the
    complex coefficient alpha_i * conj(alpha_j). -/
theorem phase_entry_frequency {I : Type*} [Fintype I] [DecidableEq I]
    (b c x : Bits I) (u v : ℝ) :
    (u * walsh b x) * (v * walsh c x) = (u * v) * walsh (b+c) x := by
  rw [walsh_add_left]
  ring

end
end VPVNP.Binary

#print axioms VPVNP.Binary.hs_shift_coords
#print axioms VPVNP.Binary.hs_energy_coords
#print axioms VPVNP.Binary.hs_sharp_bound
#print axioms VPVNP.Binary.hs_sharp_defect
#print axioms VPVNP.Binary.phase_entry_frequency
