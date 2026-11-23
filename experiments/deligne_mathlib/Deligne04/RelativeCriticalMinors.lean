import Deligne04.RelativeCriticalRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# DEL-22A: actual original-polynomial determinantal incidence ideal

For a fixed section parameter (a,c), form the augmented Jacobian
*over the original polynomial coordinate ring*, retaining the full
DEL-16 ideal. Its evaluated matrix is the true geometric Jacobian
over every field extension. All size-(d+1) minors vanish at critical
points on the stratum where the original Jacobian rank is exactly d.

The resulting ideal is a sound polynomial certificate for this
relative incidence. Sufficiency of determinant vanishing and
global elimination/projection are separate milestones.
-/

open TensorProduct Module
open scoped BigOperators

namespace Deligne22A

/-- The polynomial augmented Jacobian over K[z], before evaluation
at a geometric point, with the section-gradient row in the none slot. -/
noncomputable def polynomialAugmentedSectionMatrix
    {K : Type*} [Field K]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K) :
    Matrix (Option (Deligne16.EqCoord k r))
      (Deligne16.Coord k s) (MvPolynomial (Deligne16.Coord k s) K) :=
  fun t i => match t with
    | none => MvPolynomial.pderiv i (Deligne16.fixedSection B a c)
    | some t => MvPolynomial.pderiv i (Deligne16.copyEquation f t)

/-- Evaluation of the original polynomial augmented Jacobian is the
geometric augmented Jacobian defined using the true differential. -/
theorem polynomialAugmentedSectionMatrix_aeval
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) :
    (polynomialAugmentedSectionMatrix f B a c).map
        (MvPolynomial.aeval u).toRingHom =
      augmentedSectionMatrix f B a c u := by
  ext t i
  cases t with
  | none => rfl
  | some t => rfl

/-- Every square (d+1)-minor is an actual polynomial over K in
the original embedded-product coordinates. -/
noncomputable def augmentedMinorPolynomial
    {K : Type*} [Field K]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (d : ℕ)
    (rr : Fin (d+1) → Option (Deligne16.EqCoord k r))
    (cc : Fin (d+1) → Deligne16.Coord k s) :
    MvPolynomial (Deligne16.Coord k s) K :=
  ((polynomialAugmentedSectionMatrix f B a c).submatrix rr cc).det

/-- Evaluation of every original polynomial minor agrees exactly with
the determinant of its geometric-point augmented submatrix. -/
theorem aeval_augmentedMinorPolynomial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (d : ℕ)
    (rr : Fin (d+1) → Option (Deligne16.EqCoord k r))
    (cc : Fin (d+1) → Deligne16.Coord k s)
    (u : Deligne16.Coord k s → L) :
    MvPolynomial.aeval u (augmentedMinorPolynomial f B a c d rr cc) =
      ((augmentedSectionMatrix f B a c u).submatrix rr cc).det := by
  change (MvPolynomial.aeval u).toRingHom
      (((polynomialAugmentedSectionMatrix f B a c).submatrix rr cc).det) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact congrArg (fun A : Matrix (Option (Deligne16.EqCoord k r))
      (Deligne16.Coord k s) L => A (rr i) (cc j))
    (polynomialAugmentedSectionMatrix_aeval f B a c u)

/-- Rank at most d forces all size-(d+1) minors to vanish, even
for singular and nonreduced original Jacobian presentations. -/
theorem augmentedMinor_zero_of_rank_le
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) (d : ℕ)
    (hRank : (augmentedSectionMatrix f B a c u).rank ≤ d)
    (rr : Fin (d+1) → Option (Deligne16.EqCoord k r))
    (cc : Fin (d+1) → Deligne16.Coord k s) :
    ((augmentedSectionMatrix f B a c u).submatrix rr cc).det = 0 := by
  classical
  by_contra hdet
  have hsub : ((augmentedSectionMatrix f B a c u).submatrix rr cc).rank =
      d+1 := by
    simpa only [Fintype.card_fin] using
      (Matrix.rank_of_det_ne_zero hdet)
  have hle := Matrix.rank_submatrix_le
    (augmentedSectionMatrix f B a c u) rr cc
  omega

/-- On the original rank-d stratum, criticality on the actual tangent
forces every polynomial size-(d+1) minor to vanish over any extension. -/
theorem aeval_augmentedMinor_eq_zero_of_critical
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) (d : ℕ)
    (hrow : (originalJacobianMatrix f u).rank = d)
    (hcrit : criticalOnTangent f B a c u)
    (rr : Fin (d+1) → Option (Deligne16.EqCoord k r))
    (cc : Fin (d+1) → Deligne16.Coord k s) :
    MvPolynomial.aeval u (augmentedMinorPolynomial f B a c d rr cc) = 0 := by
  rw [aeval_augmentedMinorPolynomial]
  apply augmentedMinor_zero_of_rank_le f B a c u d
  exact (critical_iff_augmentedRank_le f B a c u d hrow).mp
    ((criticalOnTangent_iff_conormal f B a c u).mp hcrit).2.2

/-- Determinantal ideal generated by all size-(d+1) minors of the
actual polynomial augmented Jacobian at fixed section parameters. -/
noncomputable def augmentedMinorIdeal
    {K : Type*} [Field K]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K) (d : ℕ) :
    Ideal (MvPolynomial (Deligne16.Coord k s) K) :=
  Ideal.span (Set.range
    (fun rc : (Fin (d+1) → Option (Deligne16.EqCoord k r)) ×
        (Fin (d+1) → Deligne16.Coord k s) =>
      augmentedMinorPolynomial f B a c d rc.1 rc.2))

/-- Every geometric critical point on the rank-d stratum annihilates
the entire original-polynomial determinantal minor ideal. -/
theorem augmentedMinorIdeal_le_evalKer_of_critical
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) (d : ℕ)
    (hrow : (originalJacobianMatrix f u).rank = d)
    (hcrit : criticalOnTangent f B a c u) :
    augmentedMinorIdeal f B a c d ≤
      RingHom.ker (MvPolynomial.aeval u).toRingHom := by
  unfold augmentedMinorIdeal
  rw [Ideal.span_le]
  rintro _ ⟨⟨rr, cc⟩, rfl⟩
  exact RingHom.mem_ker.mpr
    (aeval_augmentedMinor_eq_zero_of_critical
      f B a c u d hrow hcrit rr cc)

/-- Affine fixed-parameter critical incidence ideal:
the original DEL-16 equations, the actual section equation, and
the size-(d+1) determinantal minors. -/
noncomputable def fixedParameterCriticalIdeal
    {K : Type*} [Field K]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K) (d : ℕ) :
    Ideal (MvPolynomial (Deligne16.Coord k s) K) :=
  (Deligne16.productIdeal f ⊔
    Ideal.span ({Deligne16.fixedSection B a c} : Set _)) ⊔
    augmentedMinorIdeal f B a c d

/-- Soundness of the fixed-parameter relative determinantal incidence
ideal on the rank-d stratum, for *all* geometric extension points.
Projected-image elimination and sufficiency require separate arguments. -/
theorem fixedParameterCriticalIdeal_le_evalKer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L) (d : ℕ)
    (hrow : (originalJacobianMatrix f u).rank = d)
    (hcrit : criticalOnTangent f B a c u) :
    fixedParameterCriticalIdeal f B a c d ≤
      RingHom.ker (MvPolynomial.aeval u).toRingHom := by
  rcases hcrit with ⟨hu, hs, _⟩
  unfold fixedParameterCriticalIdeal
  apply sup_le
  · apply sup_le
    · rw [Deligne16.productIdeal, Ideal.span_le]
      rintro _ ⟨t, rfl⟩
      exact RingHom.mem_ker.mpr (hu t)
    · rw [Ideal.span_le]
      intro q hq
      have heq : q = Deligne16.fixedSection B a c := by simpa using hq
      subst q
      exact RingHom.mem_ker.mpr hs
  · apply augmentedMinorIdeal_le_evalKer_of_critical f B a c u d hrow
    exact ⟨hu, hs, hcrit.2.2⟩

#print axioms polynomialAugmentedSectionMatrix_aeval
#print axioms aeval_augmentedMinorPolynomial
#print axioms augmentedMinor_zero_of_rank_le
#print axioms aeval_augmentedMinor_eq_zero_of_critical
#print axioms augmentedMinorIdeal_le_evalKer_of_critical
#print axioms fixedParameterCriticalIdeal_le_evalKer

end Deligne22A
