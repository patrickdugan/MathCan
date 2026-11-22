import Deligne04.Hankel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
DEL-04: exact extraction of one spectral exponential from finitely
many consecutive power traces. The coefficients are constructed by
inverting the Vandermonde matrix over the complex numbers.
-/

open scoped BigOperators Matrix
open Finset

namespace Deligne04

variable {R : Type*} [CommRing R] {s : ℕ}

/-- Rearrange a finite linear combination of trace windows as
the sum of pointwise polynomial evaluations at each eigenvalue. -/
theorem trace_window_convolution (lam weights coeff : Fin s → R)
    (n : ℕ) :
    (∑ r : Fin s, coeff r * powerTrace lam weights (n + r.val)) =
      ∑ j : Fin s, (weights j * lam j ^ n) *
        (∑ r : Fin s, coeff r * lam j ^ r.val) := by
  calc
    _ = ∑ r : Fin s, ∑ j : Fin s,
        coeff r * (weights j * lam j ^ (n + r.val)) := by
      simp only [powerTrace, Finset.mul_sum]
    _ = ∑ j : Fin s, ∑ r : Fin s,
        coeff r * (weights j * lam j ^ (n + r.val)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_add]
      ring

/-- For an injective list of complex eigenvalues, an interpolating
polynomial of degree below s isolates each eigenvalue. Its
coefficients are the inverse-Vandermonde image of an indicator vector. -/
theorem exists_isolating_coefficients
    (lam : Fin s → ℂ) (hinj : Function.Injective lam)
    (i : Fin s) :
    ∃ coeff : Fin s → ℂ,
      ∀ j : Fin s,
        (∑ r : Fin s, coeff r * lam j ^ r.val) =
          (if j = i then (1 : ℂ) else 0) := by
  have hv : (Matrix.vandermonde lam).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff).mpr hinj
  have hu : IsUnit ((Matrix.vandermonde lam).det) :=
    isUnit_iff_ne_zero.mpr hv
  have hmu : IsUnit (Matrix.vandermonde lam) :=
    (Matrix.isUnit_iff_isUnit_det).mpr hu
  obtain ⟨coeff, hcoeff⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit).mpr hmu
      (fun j : Fin s => if j = i then (1 : ℂ) else 0)
  refine ⟨coeff, ?_⟩
  intro j
  have hj := congrArg (fun v : Fin s → ℂ => v j) hcoeff
  simpa [Matrix.mulVec_apply, Matrix.vandermonde_apply,
    Matrix.dotProduct, mul_comm] using hj

/-- A chosen interpolating vector extracts the i-th weighted power
of the spectrum using s consecutive traces, for every n. -/
theorem trace_window_extract (lam weights coeff : Fin s → ℂ)
    (i : Fin s)
    (hi : ∀ j : Fin s,
      (∑ r : Fin s, coeff r * lam j ^ r.val) =
        (if j = i then (1 : ℂ) else 0))
    (n : ℕ) :
    (∑ r : Fin s, coeff r * powerTrace lam weights (n + r.val)) =
      weights i * lam i ^ n := by
  rw [trace_window_convolution]
  simp [hi]

/-- The exact spectral extraction theorem, with an existential
witness constructed over ℂ. -/
theorem exists_trace_window_extractor
    (lam weights : Fin s → ℂ)
    (hinj : Function.Injective lam)
    (i : Fin s) :
    ∃ coeff : Fin s → ℂ, ∀ n : ℕ,
      (∑ r : Fin s, coeff r * powerTrace lam weights (n + r.val)) =
        weights i * lam i ^ n := by
  obtain ⟨coeff, hc⟩ := exists_isolating_coefficients lam hinj i
  exact ⟨coeff, fun n => trace_window_extract lam weights coeff i hc n⟩

#print axioms trace_window_convolution
#print axioms exists_isolating_coefficients
#print axioms trace_window_extract
#print axioms exists_trace_window_extractor

end Deligne04
