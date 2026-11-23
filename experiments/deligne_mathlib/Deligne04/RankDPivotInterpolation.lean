import Deligne04.RelativeCriticalBaseChange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# DEL-22D: arbitrary finite-rank invertible-pivot conormal chart

For any finite row family over a field, invert a genuine d×d pivot
submatrix. The pivot columns uniquely determine the coefficients of a
vector in the chosen row span, and the remaining coordinates test membership.

The geometric theorem uses the actual original DEL-16 Jacobian rows
evaluated at a geometric extension-field point. Its selected-row-span
hypothesis is explicit; a separate rank/determinantal theorem must
produce that span assertion from a smooth rank-d stratum.

The pivot residuals here are rational functions on det(H) ≠ 0.
Polynomial Schur-complement identities and localized Fitting ideals
remain separate scheme-level obligations.
-/

open TensorProduct Module
open scoped BigOperators Matrix

namespace Deligne22D

/-- The d×d original-row pivot matrix obtained by restricting a
selected row family to d selected source coordinates. -/
noncomputable def pivotMatrix
    {L : Type*} [Field L] {ι : Type*} {d : ℕ}
    (rows : Fin d → ι → L) (cols : Fin d → ι) :
    Matrix (Fin d) (Fin d) L :=
  fun t b => rows t (cols b)

/-- The unique row-combination coefficients dictated by the pivot
coordinates on det(H) ≠ 0, written as g_C * H⁻¹. -/
noncomputable def pivotCoeffs
    {L : Type*} [Field L] {ι : Type*} {d : ℕ}
    (rows : Fin d → ι → L) (cols : Fin d → ι)
    (g : ι → L) : Fin d → L :=
  (fun b : Fin d => g (cols b)) ᵥ* (pivotMatrix rows cols)⁻¹

/-- Arbitrary-rank converse on an invertible pivot chart:
membership in the *actual selected row span* is equivalent to
interpolating every coordinate using the uniquely pivot-determined
coefficients. Valid also for d=0. -/
theorem mem_span_range_iff_pivot_residual
    {L : Type*} [Field L]
    {ι : Type*} [Fintype ι] {d : ℕ}
    (rows : Fin d → ι → L) (cols : Fin d → ι)
    (g : ι → L)
    (hdet : (pivotMatrix rows cols).det ≠ 0) :
    g ∈ Submodule.span L (Set.range rows) ↔
      ∀ j : ι,
        g j = ∑ t : Fin d, pivotCoeffs rows cols g t * rows t j := by
  classical
  have hu : IsUnit (pivotMatrix rows cols).det :=
    isUnit_iff_ne_zero.mpr hdet
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨lam, hlam⟩
    have hcols : lam ᵥ* (pivotMatrix rows cols) =
        (fun b : Fin d => g (cols b)) := by
      funext b
      have hb := congrArg (fun v : ι → L => v (cols b)) hlam
      simpa only [Matrix.vecMul_apply_eq_sum, pivotMatrix, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] using hb
    have hcoeff : lam = pivotCoeffs rows cols g := by
      have hh := congrArg
        (fun v : Fin d → L => v ᵥ* (pivotMatrix rows cols)⁻¹) hcols
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu,
        Matrix.vecMul_one, pivotCoeffs] using hh
    intro j
    have hj := congrArg (fun v : ι → L => v j) hlam
    simpa only [hcoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj.symm
  · intro h
    refine ⟨pivotCoeffs rows cols g, ?_⟩
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (h j).symm

/-- The literal original DEL-16 Jacobian rows chosen for a d×d pivot.
All redundant and nonreduced original equations remain available. -/
noncomputable def selectedOriginalRows
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r d : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (rr : Fin d → Deligne16.EqCoord k r) :
    Fin d → Deligne16.Coord k s → L :=
  fun t => Deligne21G.geometricConormalRow f u (rr t)

/-- General rank-d geometric chart. If selected *actual original*
Jacobian rows span the full conormal relation fiber, and their d×d
pivot is nonzero, vanishing of the interpolated gradient residuals
is exactly true Kähler relative criticality, with on-scheme and
on-section equations carried literally. -/
theorem criticalOnTangent_iff_rankd_pivot
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r d : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L)
    (rr : Fin d → Deligne16.EqCoord k r)
    (cc : Fin d → Deligne16.Coord k s)
    (hspan : Deligne21G.geometricConormalRelations f u =
      Submodule.span L (Set.range (selectedOriginalRows f u rr)))
    (hdet : (pivotMatrix (selectedOriginalRows f u rr) cc).det ≠ 0) :
    Deligne22A.criticalOnTangent f B a c u ↔
      Deligne21G.onGeometricProduct f u ∧
      MvPolynomial.aeval u (Deligne16.fixedSection B a c) = 0 ∧
      ∀ j : Deligne16.Coord k s,
        Deligne22A.sectionGradient B a c u j =
          ∑ t : Fin d,
            pivotCoeffs (selectedOriginalRows f u rr) cc
              (Deligne22A.sectionGradient B a c u) t *
            selectedOriginalRows f u rr t j := by
  rw [Deligne22A.criticalOnTangent_iff_conormal]
  constructor
  · rintro ⟨hu, hs, hg⟩
    refine ⟨hu, hs, ?_⟩
    rw [hspan] at hg
    exact (mem_span_range_iff_pivot_residual
      (selectedOriginalRows f u rr) cc
      (Deligne22A.sectionGradient B a c u) hdet).mp hg
  · rintro ⟨hu, hs, hq⟩
    refine ⟨hu, hs, ?_⟩
    rw [hspan]
    exact (mem_span_range_iff_pivot_residual
      (selectedOriginalRows f u rr) cc
      (Deligne22A.sectionGradient B a c u) hdet).mpr hq

#print axioms mem_span_range_iff_pivot_residual
#print axioms criticalOnTangent_iff_rankd_pivot

end Deligne22D
