module

public import TRR08Geometry.DiagonalSlope
public import TRR08Geometry.FiniteSlopeAverage
public import TRR08Geometry.LocalCoefficient
public import TRR08Geometry.Obstruction

/-!
# The obstruction for explicit finite slope coefficients

The coefficient used here is the negative sum of actual normalized slopes
over the given finite subgroup. Its doubling identity follows from the
proved diagonal identity on Mathlib's point group. The tame exclusion
therefore asks only for the square identity at the nonidentity multiples.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

/-- Finite averaging of the proved diagonal identity gives the doubling law
for the explicit slope coefficient on any finite subgroup. -/
theorem slopeCoefficient_double (H : AddSubgroup W.Point) [Fintype H] (P : H) :
    slopeCoefficient H (P + P) = 2 * slopeCoefficient H P +
      (Fintype.card H : K) * normalizedSlope (P : W.Point) (P : W.Point) := by
  have hs := FiniteSlopeAverage.coefficient_double_of_diagonal
    (fun P Q : H => normalizedSlope (P : W.Point) (Q : W.Point)) P
    (fun R => normalizedSlope_diagonal (P : W.Point) (R : W.Point))
  simpa only [FiniteSlopeAverage.coefficient, FiniteSlopeAverage.rowSum,
    slopeCoefficient, AddSubgroup.coe_add] using hs

theorem slopeCoefficient_double_tangent (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hD : P + P ≠ 0) :
    slopeCoefficient H (P + P) = 2 * slopeCoefficient H P +
      (Fintype.card H : K) *
        ((3 * affineX (P : W.Point)^2 + W.a₄) / (2 * affineY (P : W.Point))) := by
  have hp : (P : W.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hd : (P : W.Point) + (P : W.Point) ≠ 0 := fun h => hD (Subtype.ext h)
  rw [slopeCoefficient_double, normalizedSlope_self hp hd]

/-- The reciprocal-root coefficient inherits the actual doubling law on an
odd subgroup, wherever the tangent denominator is nonzero. -/
theorem localCoefficient_double (H : AddSubgroup W.Point) [Fintype H]
    (P : H) (hP : P ≠ 0) (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q)
    (h₂ : (2 : K) ≠ 0) :
    localCoefficient H (P + P) = 2 * localCoefficient H P +
      (Fintype.card H : K) *
        ((3 * affineX (P : W.Point)^2 + W.a₄) / (2 * affineY (P : W.Point))) := by
  have hD : P + P ≠ 0 := by
    intro h
    exact hno2 P hP (eq_neg_iff_add_eq_zero.mpr h)
  rw [localCoefficient_eq_slopeCoefficient H (P + P) hD hno2 h₂,
    localCoefficient_eq_slopeCoefficient H P hP hno2 h₂]
  exact slopeCoefficient_double_tangent H P hP hD

/-- The concrete coefficient sequence on the actual cyclic subgroup of `T`. -/
noncomputable def cyclicSlopeCoefficient (T : W.Point) (hT : IsOfFinAddOrder T)
    (k : ℕ) : K :=
  FiniteSlopeAverage.cyclicCoefficient normalizedSlope T hT k

/-- No scalar cardinal is inverted in this identity. -/
theorem cyclicSlopeCoefficient_double (T : W.Point) (hT : IsOfFinAddOrder T)
    (k : ℕ) :
    cyclicSlopeCoefficient T hT (2 * k) = 2 * cyclicSlopeCoefficient T hT k +
      (addOrderOf T : K) * normalizedSlope (k • T) (k • T) := by
  exact FiniteSlopeAverage.cyclicCoefficient_double_of_diagonal normalizedSlope T hT k
    (fun R => normalizedSlope_diagonal (k • T) (R : W.Point))

theorem cyclicSlopeCoefficient_double_tangent (T : W.Point) (hT : IsOfFinAddOrder T)
    (k : ℕ) (hP : k • T ≠ 0) (hD : k • T + k • T ≠ 0) :
    cyclicSlopeCoefficient T hT (2 * k) = 2 * cyclicSlopeCoefficient T hT k +
      (addOrderOf T : K) *
        ((3 * affineX (k • T)^2 + W.a₄) / (2 * affineY (k • T))) := by
  rw [cyclicSlopeCoefficient_double, normalizedSlope_self hP hD]

/-- The square identity for the explicit finite slope coefficient is
incompatible with a tame smooth marked point of order at least nineteen. -/
theorem tame_cyclicSlopeCoefficient_exclusion [W.IsElliptic]
    (T : W.Point) (hfin : IsOfFinAddOrder T) (hT : 19 ≤ addOrderOf T)
    (hn : (addOrderOf T : K) ≠ 0) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (c : K)
    (hconstant : ∀ k : ℕ, k • T ≠ 0 →
      cyclicSlopeCoefficient T hfin k ^ 2 =
        (addOrderOf T : K) * (affineX (k • T) + c)) :
    False := by
  exact tame_coefficient_exclusion T hT hn h₂ h₃
    (cyclicSlopeCoefficient T hfin) c hconstant
    (cyclicSlopeCoefficient_double_tangent T hfin)

end TRR08Geometry

#print axioms TRR08Geometry.slopeCoefficient_double
#print axioms TRR08Geometry.slopeCoefficient_double_tangent
#print axioms TRR08Geometry.localCoefficient_double
#print axioms TRR08Geometry.cyclicSlopeCoefficient_double
#print axioms TRR08Geometry.cyclicSlopeCoefficient_double_tangent
#print axioms TRR08Geometry.tame_cyclicSlopeCoefficient_exclusion
