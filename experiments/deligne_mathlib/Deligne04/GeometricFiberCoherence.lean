import Deligne04.GeometricFiberNaturality
import Mathlib.Tactic

/-!
# DEL-21I: coordinate coherence for the geometric cotangent-tangent duality

The first refinement identifies the coordinate of DEL-21G's quotient-dual
equivalence directly with evaluation on the original coordinate class.
The quotient and Jacobian tangent remain those of the complete DEL-16
defining ideal, with nilpotent and redundant equations retained.
-/

open TensorProduct Module

namespace Deligne21I

/-- A functional on the actual geometric conormal quotient corresponds to
the original Jacobian tangent vector whose i-th coordinate is its value
on the class of the i-th coordinate basis vector. -/
theorem geometricCotangentDualEquivTangent_coord
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (ψ : Module.Dual L (Deligne21G.geometricCotangentFiber f u))
    (i : Deligne16.Coord k s) :
    ((Deligne21G.geometricCotangentDualEquivTangent f u ψ :
        Deligne21G.geometricJacobianTangent f u) :
        Deligne16.Coord k s → L) i =
      ψ (Submodule.Quotient.mk (Pi.single i (1 : L))) := by
  classical
  change ((Deligne21G.geometricConormalRelations f u).dualQuotEquivDualAnnihilator ψ :
      Module.Dual L (Deligne16.Coord k s → L))
      (Pi.single i (1 : L)) =
        ψ (Submodule.Quotient.mk (Pi.single i (1 : L)))
  exact Submodule.dualQuotEquivDualAnnihilator_apply _ _ _

#print axioms geometricCotangentDualEquivTangent_coord

end Deligne21I
