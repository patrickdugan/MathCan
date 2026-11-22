import Deligne04.PresentedCotangentFiber
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.RingTheory.Ideal.Quotient.Over
import Mathlib.Tactic

/-!
# DEL-21E: an actual quotient-ring algebra presentation of U^k

DEL-21D builds the conormal quotient of the polynomial Jacobian
and proves its dual equals the actual tangent kernel. To connect
this object to the genuine Kähler module, one first needs an
algebra presentation of the **true quotient ring**
A=K[coordinates of U^k]/(actual lifted defining polynomials).

This file constructs that presentation with precisely the
original DEL-16 polynomial generators and their full ideal,
using Mathlib's quotient algebra and Algebra.Generators.ofAlgHom.

Mathlib's Algebra.Presentation.differentials then gives an
actual Module.Presentation A Ω[A⁄K], with differential relations
obtained from the true multivariate partial derivatives.

The next theorem will base-change this module presentation
along a rational point u:A→ₐ[K]K and identify its fiber's
relation span with DEL-21D.conormalRelations f u.
-/

namespace Deligne21E

/-- The genuine quotient coordinate ring of U^k as presented
by DEL-16's original lifted defining ideal. -/
abbrev productCoordinateRing
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K) :=
  (MvPolynomial (Deligne16.Coord k s) K ⧸ Deligne16.productIdeal f)

/-- Actual polynomial algebra presentation of the quotient ring.
Its relations are the unmodified lifted defining equations of U^k;
they generate precisely the quotient ideal, including nilpotents. -/
noncomputable def productAlgebraPresentation
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K) :
    Algebra.Presentation K
      (productCoordinateRing (k := k) f) (Deligne16.Coord k s)
        (Deligne16.EqCoord k r) := by
  classical
  let I : Ideal (MvPolynomial (Deligne16.Coord k s) K) := Deligne16.productIdeal f
  let Q : MvPolynomial (Deligne16.Coord k s) K →ₐ[K]
      productCoordinateRing (k := k) f := Ideal.Quotient.mkₐ K I
  have hQ : Function.Surjective Q := Ideal.Quotient.mk_surjective I
  let G : Algebra.Generators K (productCoordinateRing (k := k) f)
      (Deligne16.Coord k s) := Algebra.Generators.ofAlgHom Q hQ
  refine {
    toGenerators := G
    relation := Deligne16.copyEquation f
    span_range_relation_eq_ker := ?_ }
  change I = G.ker
  rw [show G.ker = RingHom.ker Q.toRingHom from
    Algebra.Generators.ker_ofAlgHom Q hQ]
  exact (Ideal.mk_ker).symm

/-- A genuine presentation of the Kähler differential module
of the *actual* quotient algebra A=K[z]/I. This invokes Mathlib's
kernel-verified Kähler-presentation construction and its conormal
exact-sequence theorem rather than a symbolic stand-in. -/
noncomputable def productKahlerPresentation
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K) :
    Module.Presentation (productCoordinateRing (k := k) f)
      Ω[productCoordinateRing (k := k) f⁄K] :=
  (productAlgebraPresentation (k := k) f).differentials

/-- The quotient-ring presentation has exactly the original
number of ambient variables and relation indices. -/
theorem product_presentation_indices
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K) :
    (productKahlerPresentation (k := k) f).G = Deligne16.Coord k s ∧
      (productKahlerPresentation (k := k) f).R = Deligne16.EqCoord k r := by
  exact ⟨rfl, rfl⟩

#print axioms product_presentation_indices

end Deligne21E
