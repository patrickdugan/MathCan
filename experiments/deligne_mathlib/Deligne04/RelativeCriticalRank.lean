import Deligne04.GeometricIdentityCoherence
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-!
# DEL-22A: original-ideal relative criticality and augmented Jacobian rank

The DEL-16 product coordinate algebra and every original lifted equation
are retained. At an arbitrary field-extension point, a section is
critical on the actual DEL-21G Jacobian tangent space if and only if
its original-polynomial gradient lies in the conormal relation span.
The resulting augmented matrix has the same rank as the original
Jacobian. This is the rank-stratum prerequisite for determinantal /
Fitting ideals in the relative Bertini incidence.
-/

open TensorProduct Module
open scoped BigOperators

namespace Deligne22A

/-- A finite-coordinate linear functional annihilates the annihilator
tangent subspace exactly when its coefficient vector is in the original
relation subspace. This uses genuine dual separation over a field. -/
theorem mem_conormal_iff_annihilates_tangent
    {L : Type*} [Field L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Subspace L (ι → L)) (g : ι → L) :
    g ∈ R ↔
      ∀ v : ι → L,
        v ∈ R.dualAnnihilator.comap
          ((LinearEquiv.piRing L L ι L).symm.toLinearMap) →
        (∑ i : ι, g i * v i) = 0 := by
  classical
  let E := LinearEquiv.piRing L L ι L
  have hpair (v : ι → L) :
      (E.symm v) g = ∑ i : ι, g i * v i := by
    simp only [E, LinearEquiv.piRing_symm_apply, smul_eq_mul]
  constructor
  · intro hg v hv
    have hv' : E.symm v ∈ R.dualAnnihilator := hv
    have hz : (E.symm v) g = 0 :=
      ((Submodule.mem_dualAnnihilator (E.symm v)).mp hv') g hg
    exact (hpair v).symm.trans hz
  · intro hv
    apply (R.forall_mem_dualAnnihilator_apply_eq_zero_iff g).mp
    intro φ hφ
    have ht : E φ ∈ R.dualAnnihilator.comap E.symm.toLinearMap := by
      change E.symm (E φ) ∈ R.dualAnnihilator
      simpa only [E.symm_apply_apply] using hφ
    have h := hv (E φ) ht
    have he := hpair (E φ)
    rw [E.symm_apply_apply] at he
    exact he.trans h

/-- The original DEL-16 fixed-coefficient section's actual evaluated
gradient, using formal polynomial partial derivatives over K. -/
noncomputable def sectionGradient
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s : ℕ}
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) :
    Deligne16.Coord k s → L :=
  fun i => MvPolynomial.aeval u
    (MvPolynomial.pderiv i (Deligne16.fixedSection B a c))

/-- Criticality of the actual pulled-back section at a geometric point:
its derivative vanishes on every vector in the full-ideal Jacobian tangent. -/
def criticalOnTangent
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) : Prop :=
  Deligne21G.onGeometricProduct f u ∧
    MvPolynomial.aeval u (Deligne16.fixedSection B a c) = 0 ∧
    ∀ v : Deligne16.Coord k s → L,
      v ∈ Deligne21G.geometricJacobianTangent f u →
      (∑ i : Deligne16.Coord k s, sectionGradient B a c u i * v i) = 0

/-- The same relative incidence expressed as actual membership of
the section derivative in the original conormal relation space. -/
def criticalInConormal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) : Prop :=
  Deligne21G.onGeometricProduct f u ∧
    MvPolynomial.aeval u (Deligne16.fixedSection B a c) = 0 ∧
    sectionGradient B a c u ∈ Deligne21G.geometricConormalRelations f u

/-- Criticality on the Jacobian tangent equals original-ideal
conormal membership, for all field extensions and every characteristic.
The equivalence is valid even when the original scheme is nonreduced. -/
theorem criticalOnTangent_iff_conormal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) :
    criticalOnTangent f B a c u ↔ criticalInConormal f B a c u := by
  constructor
  · rintro ⟨hu, hs, hder⟩
    refine ⟨hu, hs, ?_⟩
    exact (mem_conormal_iff_annihilates_tangent
      (Deligne21G.geometricConormalRelations f u)
      (sectionGradient B a c u)).mpr hder
  · rintro ⟨hu, hs, hg⟩
    refine ⟨hu, hs, ?_⟩
    exact (mem_conormal_iff_annihilates_tangent
      (Deligne21G.geometricConormalRelations f u)
      (sectionGradient B a c u)).mp hg

/-- Being in the original conormal span is the existence of a finite
list of true Lagrange multipliers for each original Jacobian row.
No smooth-complete-intersection rank assumption is needed here. -/
theorem sectionGradient_mem_conormal_iff_lagrange
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) :
    sectionGradient B a c u ∈ Deligne21G.geometricConormalRelations f u ↔
      ∃ lam : Deligne16.EqCoord k r → L,
        ∀ i : Deligne16.Coord k s,
          sectionGradient B a c u i =
            ∑ t : Deligne16.EqCoord k r,
              lam t * Deligne21G.geometricConormalRow f u t i := by
  classical
  change sectionGradient B a c u ∈
      Submodule.span L (Set.range (Deligne21G.geometricConormalRow f u)) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨lam, h⟩
    refine ⟨lam, fun i => ?_⟩
    have hcoord := congrArg
      (fun w : Deligne16.Coord k s → L => w i) h
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoord.symm
  · rintro ⟨lam, h⟩
    refine ⟨lam, ?_⟩
    funext i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (h i).symm

/-- The concrete original Jacobian matrix at an L-valued point,
with all lifted original polynomial equations in their given order. -/
noncomputable def originalJacobianMatrix
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) :
    Matrix (Deligne16.EqCoord k r) (Deligne16.Coord k s) L :=
  fun t i => Deligne21G.geometricConormalRow f u t i

/-- The augmented Jacobian has one extra row, the actual derivative
of the specified original-polynomial section. -/
noncomputable def augmentedSectionMatrix
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) :
    Matrix (Option (Deligne16.EqCoord k r)) (Deligne16.Coord k s) L :=
  fun t i => match t with
    | none => sectionGradient B a c u i
    | some t => Deligne21G.geometricConormalRow f u t i

/-- All rows of the original Jacobian occur in the augmented row span. -/
theorem originalConormal_le_augmentedSpan
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) :
    Deligne21G.geometricConormalRelations f u ≤
      Submodule.span L (Set.range (augmentedSectionMatrix f B a c u).row) := by
  classical
  change Submodule.span L (Set.range (Deligne21G.geometricConormalRow f u)) ≤ _
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  apply Submodule.subset_span
  exact ⟨some t, rfl⟩

/-- The augmented rows span exactly the original conormal relations
iff the added actual section gradient is already conormal. -/
theorem augmentedSpan_eq_conormal_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) :
    Submodule.span L (Set.range (augmentedSectionMatrix f B a c u).row) =
      Deligne21G.geometricConormalRelations f u ↔
      sectionGradient B a c u ∈ Deligne21G.geometricConormalRelations f u := by
  classical
  constructor
  · intro heq
    have hg : sectionGradient B a c u ∈
        Submodule.span L (Set.range (augmentedSectionMatrix f B a c u).row) := by
      apply Submodule.subset_span
      exact ⟨none, rfl⟩
    rwa [heq] at hg
  · intro hg
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨t, rfl⟩
      cases t with
      | none =>
          exact hg
      | some t =>
          change Deligne21G.geometricConormalRow f u t ∈
            Deligne21G.geometricConormalRelations f u
          exact Submodule.subset_span (Set.mem_range_self t)
    · exact originalConormal_le_augmentedSpan f B a c u

/-- At an arbitrary original-scheme field-extension point, appending
the actual section derivative leaves the rank unchanged precisely when
the section's differential is conormal to the original product. -/
theorem augmentedRank_eq_iff_conormal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) :
    (augmentedSectionMatrix f B a c u).rank =
      (originalJacobianMatrix f u).rank ↔
    sectionGradient B a c u ∈ Deligne21G.geometricConormalRelations f u := by
  classical
  rw [(augmentedSectionMatrix f B a c u).rank_eq_finrank_span_row,
      (originalJacobianMatrix f u).rank_eq_finrank_span_row]
  change Module.finrank L
      (Submodule.span L (Set.range (augmentedSectionMatrix f B a c u).row)) =
      Module.finrank L (Deligne21G.geometricConormalRelations f u) ↔ _
  constructor
  · intro h
    have hle := originalConormal_le_augmentedSpan f B a c u
    have heq : Deligne21G.geometricConormalRelations f u =
        Submodule.span L (Set.range (augmentedSectionMatrix f B a c u).row) :=
      Submodule.eq_of_le_of_finrank_eq hle h.symm
    exact (augmentedSpan_eq_conormal_iff f B a c u).mp heq.symm
  · intro hg
    rw [(augmentedSpan_eq_conormal_iff f B a c u).mpr hg]

/-- On any stratum where the original Jacobian has rank d,
the relative criticality equation is precisely an upper rank bound
on the original augmented matrix, the condition encoded by the
size-(d+1) determinantal minors. -/
theorem critical_iff_augmentedRank_le
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) (d : ℕ)
    (hrow : (originalJacobianMatrix f u).rank = d) :
    sectionGradient B a c u ∈ Deligne21G.geometricConormalRelations f u ↔
      (augmentedSectionMatrix f B a c u).rank ≤ d := by
  classical
  have hle : (originalJacobianMatrix f u).rank ≤
      (augmentedSectionMatrix f B a c u).rank := by
    rw [(originalJacobianMatrix f u).rank_eq_finrank_span_row,
        (augmentedSectionMatrix f B a c u).rank_eq_finrank_span_row]
    change Module.finrank L (Deligne21G.geometricConormalRelations f u) ≤
      Module.finrank L
        (Submodule.span L (Set.range (augmentedSectionMatrix f B a c u).row))
    exact Submodule.finrank_mono (originalConormal_le_augmentedSpan f B a c u)
  constructor
  · intro hg
    have heq := (augmentedRank_eq_iff_conormal f B a c u).mpr hg
    exact le_of_eq (heq.trans hrow)
  · intro h
    apply (augmentedRank_eq_iff_conormal f B a c u).mp
    apply Nat.le_antisymm
    · exact h.trans hrow.symm.le
    · exact hle

/-- The actual DEL-16 relative critical incidence is equivalent to the
original augmented-Jacobian rank equation at arbitrary extension points,
including positive characteristic and nonreduced cases. -/
theorem criticalOnTangent_iff_augmentedRank
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) :
    criticalOnTangent f B a c u ↔
      Deligne21G.onGeometricProduct f u ∧
        MvPolynomial.aeval u (Deligne16.fixedSection B a c) = 0 ∧
        (augmentedSectionMatrix f B a c u).rank =
          (originalJacobianMatrix f u).rank := by
  constructor
  · intro h
    rcases (criticalOnTangent_iff_conormal f B a c u).mp h
      with ⟨hu, hs, hg⟩
    exact ⟨hu, hs, (augmentedRank_eq_iff_conormal f B a c u).mpr hg⟩
  · rintro ⟨hu, hs, hr⟩
    apply (criticalOnTangent_iff_conormal f B a c u).mpr
    exact ⟨hu, hs, (augmentedRank_eq_iff_conormal f B a c u).mp hr⟩

#print axioms mem_conormal_iff_annihilates_tangent
#print axioms criticalOnTangent_iff_conormal
#print axioms sectionGradient_mem_conormal_iff_lagrange
#print axioms augmentedSpan_eq_conormal_iff
#print axioms augmentedRank_eq_iff_conormal
#print axioms critical_iff_augmentedRank_le
#print axioms criticalOnTangent_iff_augmentedRank

end Deligne22A
