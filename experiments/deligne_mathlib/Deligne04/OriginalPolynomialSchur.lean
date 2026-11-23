import Deligne04.PolynomialSchurNumerator
import Mathlib.Tactic

/-!
# DEL-22E: the literal DEL-16 polynomial Jacobian Schur chart

The pivot block uses pderiv of each actual DEL-16 product equation
over K[z], retaining every redundant and nonreduced relation. The
bottom row uses pderiv of DEL-16's actual fixed-last-coefficient section.

Its determinant is a genuine polynomial before geometric evaluation.
The numerator is another genuine polynomial, built from det(H) and
adj(H) with no division. Both specialize to the corresponding
extension-field matrices through RingHom.map_det and map_adjugate.
-/

open TensorProduct Module
open scoped Matrix BigOperators

namespace Deligne22E

/-- Selected original equation derivatives form the literal polynomial
Jacobian pivot H over K[z]. -/
noncomputable def fixedPolynomialPivotH
    {K : Type*} [Field K] {k s r d : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (rr : Fin d → Deligne16.EqCoord k r)
    (cc : Fin d → Deligne16.Coord k s) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Deligne16.Coord k s) K) :=
  fun t b => MvPolynomial.pderiv (cc b) (Deligne16.copyEquation f (rr t))

/-- Original polynomial Jacobian column at any source coordinate. -/
noncomputable def fixedPolynomialPivotB
    {K : Type*} [Field K] {k s r d : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (rr : Fin d → Deligne16.EqCoord k r)
    (j : Deligne16.Coord k s) :
    Fin d → MvPolynomial (Deligne16.Coord k s) K :=
  fun t => MvPolynomial.pderiv j (Deligne16.copyEquation f (rr t))

/-- Polynomial section-gradient row at the selected pivot columns. -/
noncomputable def fixedPolynomialPivotC
    {K : Type*} [Field K] {k s d : ℕ}
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (cc : Fin d → Deligne16.Coord k s) :
    Fin d → MvPolynomial (Deligne16.Coord k s) K :=
  fun b => MvPolynomial.pderiv (cc b) (Deligne16.fixedSection B a c)

/-- Polynomial section derivative at the extra source coordinate. -/
noncomputable def fixedPolynomialPivotV
    {K : Type*} [Field K] {k s : ℕ}
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (j : Deligne16.Coord k s) :
    MvPolynomial (Deligne16.Coord k s) K :=
  MvPolynomial.pderiv j (Deligne16.fixedSection B a c)

/-- The original bordered Jacobian determinant is a literal polynomial
over K[z], with the selected original rows and the section gradient. -/
noncomputable def fixedPolynomialPivotMinor
    {K : Type*} [Field K] {k s r d : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (rr : Fin d → Deligne16.EqCoord k r)
    (cc : Fin d → Deligne16.Coord k s)
    (j : Deligne16.Coord k s) :
    MvPolynomial (Deligne16.Coord k s) K :=
  (borderedPivot (fixedPolynomialPivotH f rr cc)
    (fixedPolynomialPivotB f rr j)
    (fixedPolynomialPivotC B a c cc)
    (fixedPolynomialPivotV B a c j)).det

/-- Its polynomial Schur numerator is defined on the *whole* original
scheme coordinate ring, even at singular or nonreduced points. -/
noncomputable def fixedPolynomialPivotNumerator
    {K : Type*} [Field K] {k s r d : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (rr : Fin d → Deligne16.EqCoord k r)
    (cc : Fin d → Deligne16.Coord k s)
    (j : Deligne16.Coord k s) :
    MvPolynomial (Deligne16.Coord k s) K :=
  pivotNumerator (fixedPolynomialPivotH f rr cc)
    (fixedPolynomialPivotB f rr j)
    (fixedPolynomialPivotC B a c cc)
    (fixedPolynomialPivotV B a c j)

/-- Each original polynomial bordered minor specializes exactly to
the same bordered minor of the true extension-field Jacobian, before
assuming rank, smoothness, or a nonzero pivot. -/
theorem aeval_fixedPolynomialPivotMinor
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r d : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L)
    (rr : Fin d → Deligne16.EqCoord k r)
    (cc : Fin d → Deligne16.Coord k s)
    (j : Deligne16.Coord k s) :
    MvPolynomial.aeval u (fixedPolynomialPivotMinor f B a c rr cc j) =
      (borderedPivot
        (Deligne22D.pivotMatrix (Deligne22D.selectedOriginalRows f u rr) cc)
        (fun t => Deligne22D.selectedOriginalRows f u rr t j)
        (fun b => Deligne22A.sectionGradient B a c u (cc b))
        (Deligne22A.sectionGradient B a c u j)).det := by
  unfold fixedPolynomialPivotMinor
  rw [det_borderedPivot_map (MvPolynomial.aeval u).toRingHom]
  rfl

/-- The polynomial numerator also specializes exactly, through
determinant/adjugate naturality under every field map. -/
theorem aeval_fixedPolynomialPivotNumerator
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r d : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L)
    (rr : Fin d → Deligne16.EqCoord k r)
    (cc : Fin d → Deligne16.Coord k s)
    (j : Deligne16.Coord k s) :
    MvPolynomial.aeval u (fixedPolynomialPivotNumerator f B a c rr cc j) =
      pivotNumerator
        (Deligne22D.pivotMatrix (Deligne22D.selectedOriginalRows f u rr) cc)
        (fun t => Deligne22D.selectedOriginalRows f u rr t j)
        (fun b => Deligne22A.sectionGradient B a c u (cc b))
        (Deligne22A.sectionGradient B a c u j) := by
  unfold fixedPolynomialPivotNumerator
  rw [pivotNumerator_map (MvPolynomial.aeval u).toRingHom]
  rfl

/-- On any nonzero original Jacobian pivot over a geometric field,
the evaluated actual polynomial bordered minor is exactly the
Schur numerator of the true conormal rows and section derivative. -/
theorem aeval_fixedPolynomialPivotMinor_eq_numerator_of_pivot
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r d : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K)
    (u : Deligne16.Coord k s → L)
    (rr : Fin d → Deligne16.EqCoord k r)
    (cc : Fin d → Deligne16.Coord k s)
    (j : Deligne16.Coord k s)
    (hdet : (Deligne22D.pivotMatrix
      (Deligne22D.selectedOriginalRows f u rr) cc).det ≠ 0) :
    MvPolynomial.aeval u (fixedPolynomialPivotMinor f B a c rr cc j) =
      pivotNumerator
        (Deligne22D.pivotMatrix (Deligne22D.selectedOriginalRows f u rr) cc)
        (fun t => Deligne22D.selectedOriginalRows f u rr t j)
        (fun b => Deligne22A.sectionGradient B a c u (cc b))
        (Deligne22A.sectionGradient B a c u j) := by
  rw [aeval_fixedPolynomialPivotMinor]
  exact det_borderedPivot_eq_numerator_of_det_ne_zero _ _ _ _ hdet

#print axioms aeval_fixedPolynomialPivotMinor
#print axioms aeval_fixedPolynomialPivotNumerator
#print axioms aeval_fixedPolynomialPivotMinor_eq_numerator_of_pivot

end Deligne22E
