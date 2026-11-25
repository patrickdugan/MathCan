module

public import TRR08Geometry.MarkedPoints
public import MathCan.TranslationInterpolationRootBound
public import Mathlib.Data.List.FinRange

/-!
# The uniform obstruction on actual Weierstrass points

The curve, group law, marked-point order, coordinate distinctness, curve
equation, tangent denominator and doubling coordinate are concrete Mathlib
objects or proved facts. The two remaining hypotheses explicitly concern
the geometric local coefficients: their square identity and their doubling
cocycle. The global residue and logarithmic-divisor constructions which
produce those coefficients are not asserted by this module.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type} [Field K] [DecidableEq K] {W : Affine K}
  [W.IsShortNF] [W.IsElliptic]

/-- On an actual smooth short Weierstrass curve, the two local-coefficient
    identities are incompatible at marked order at least nineteen in tame
    characteristic. The hypotheses involve only multiples of the marked
    point, so they require no extension of the coefficient function to the
    whole curve. -/
theorem tame_coefficient_exclusion (T : W.Point) (hT : 19 ≤ addOrderOf T)
    (hn : (addOrderOf T : K) ≠ 0) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (a : ℕ → K) (c : K)
    (hconstant : ∀ k : ℕ, k • T ≠ 0 →
      a k ^ 2 = (addOrderOf T : K) * (affineX (k • T) + c))
    (hcocycle : ∀ k : ℕ, k • T ≠ 0 → (k • T) + (k • T) ≠ 0 →
      a (2 * k) = 2 * a k + (addOrderOf T : K) *
        ((3 * affineX (k • T) ^ 2 + W.a₄) / (2 * affineY (k • T)))) :
    False := by
  let roots : List K := List.ofFn (fun i : Fin 9 => affineX (firstNine T i))
  have hdistinct : roots.Nodup :=
    List.nodup_ofFn.mpr (firstNine_x_injective T hT)
  have hlen : 9 ≤ roots.length := by simp [roots]
  apply short_discriminant_ne_zero (W := W)
  apply MathCan.TranslationInterpolationRootBound.doubling_data_force_singularity
    (addOrderOf T : K) W.a₄ W.a₆ c roots hn h₂ h₃ hdistinct hlen
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  let k : ℕ := i.val + 1
  let P : W.Point := firstNine T i
  have hP : P ≠ 0 := firstNine_ne_zero T hT i
  have hdouble : P + P ≠ 0 := by
    intro hz
    exact firstNine_ne_neg T hT i i ((eq_neg_iff_add_eq_zero).2 hz)
  have hdoubled : (2 * k) • T = P + P := by
    dsimp [k, P, firstNine]
    rw [mul_nsmul, two_nsmul, nsmul_add]
  let m : K := (3 * affineX P ^ 2 + W.a₄) / (2 * affineY P)
  refine ⟨affineY P, a k, m, affineX (P + P), a (2 * k),
    (short_curve_equation hP).symm, ?_, short_doubling_x hP hdouble,
    hcocycle k hP hdouble, hconstant k hP, ?_⟩
  · have hy : 2 * affineY P ≠ 0 := mul_ne_zero h₂ (short_y_ne_zero hP hdouble)
    dsimp [m]
    rw [mul_div_cancel₀ _ hy]
  · have hd : (2 * k) • T ≠ 0 := hdoubled ▸ hdouble
    simpa only [hdoubled] using hconstant (2 * k) hd

end TRR08Geometry

#print axioms TRR08Geometry.tame_coefficient_exclusion
