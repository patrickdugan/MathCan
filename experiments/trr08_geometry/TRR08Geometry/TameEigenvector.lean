module

public import TRR08Geometry.CyclicCoefficient
public import TRR08Geometry.ResidueEigenvector

/-!
# Excluding the actual residue eigenvector on a tame odd cyclic subgroup

The hypothesis below is the concrete matrix row equation with the original
inverse tangent-times-root-product residues. The proof derives the square
identity from that row equation and the finite coordinate trace, then uses
the proved slope doubling identity and the nine-point obstruction.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

/-- The actual residue vector is an eigenvector of the coordinate-sum matrix
on every nonidentity point of the cyclic subgroup. The identity point has
residue zero and coordinate zero in `residueMatrixRow`. -/
noncomputable def cyclicResidueEigenvector (T : W.Point)
    (hfin : IsOfFinAddOrder T) (u : K) : Prop :=
  letI := FiniteSlopeAverage.cyclicFintype T hfin;
  ∀ P : AddSubgroup.zmultiples T, P ≠ 0 →
    residueMatrixRow (AddSubgroup.zmultiples T) P =
      u * subgroupResidue (AddSubgroup.zmultiples T) P

/-- The complete tame exclusion has an actual residue eigenvector as its
only interpolation premise. Its coefficient and trace identities are proved
from the finite subgroup and the Weierstrass addition law. -/
theorem tame_cyclicResidue_eigenvector_exclusion [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hodd : Odd (addOrderOf T)) (hn : (addOrderOf T : K) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (u : K)
    (heigen : cyclicResidueEigenvector T hfin u) : False := by
  let := FiniteSlopeAverage.cyclicFintype T hfin
  let H := AddSubgroup.zmultiples T
  have he : ∀ P : H, P ≠ 0 → residueMatrixRow H P = u * subgroupResidue H P := heigen
  let c : K := (2 * u - subgroupXTrace H) / (addOrderOf T : K)
  apply tame_cyclicSlopeCoefficient_exclusion T hfin hT hn h₂ h₃ c
  intro k hk
  let P : H := cyclicMultiple T k
  have hP : P ≠ 0 := fun h => hk (congrArg Subtype.val h)
  have hs := residue_eigenvector_square H P hP
    (cyclic_ne_neg_of_odd_order T hodd) h₂ u (he P hP)
  have hsc : slopeCoefficient H P = cyclicSlopeCoefficient T hfin k := rfl
  rw [hsc, FiniteSlopeAverage.cyclic_card T hfin] at hs
  change cyclicSlopeCoefficient T hfin k ^ 2 =
    (addOrderOf T : K) * affineX (k • T) + 2 * u - subgroupXTrace H at hs
  calc
    cyclicSlopeCoefficient T hfin k ^ 2 =
        (addOrderOf T : K) * affineX (k • T) + 2 * u - subgroupXTrace H := hs
    _ = (addOrderOf T : K) * (affineX (k • T) + c) := by
      dsimp [c]
      field_simp
      ring

/-- There is no eigenvalue over the field for the concrete residue vector. -/
theorem tame_no_cyclicResidue_eigenvector [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hodd : Odd (addOrderOf T)) (hn : (addOrderOf T : K) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) :
    ¬ ∃ u : K, cyclicResidueEigenvector T hfin u := by
  rintro ⟨u, heigen⟩
  exact tame_cyclicResidue_eigenvector_exclusion T hfin hT hodd hn h₂ h₃ u heigen

end TRR08Geometry

#print axioms TRR08Geometry.tame_cyclicResidue_eigenvector_exclusion
#print axioms TRR08Geometry.tame_no_cyclicResidue_eigenvector
