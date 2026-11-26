module

public import TRR08Geometry.BlockTensor

/-!
# Ordinary block degree under affine coordinate changes

Each transformed monomial is built from bivariate affine powers. Their
explicit tensor sum gives an actual four-variable polynomial with the same
ordinary degree bound in each input pair. Affine changes of the output also
preserve the bound, including degree zero.
-/

@[expose] public section

namespace TRR08Geometry

open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def affineBivariateX (α r : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C α * MvPolynomial.X 0 + MvPolynomial.C r

noncomputable def affineBivariateY (β s t : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C β * MvPolynomial.X 1 +
    MvPolynomial.C s * MvPolynomial.X 0 + MvPolynomial.C t

theorem affineBivariateX_eval (α r x y : K) :
    bivariateEval (affineBivariateX α r) x y = α*x+r := by
  simp [bivariateEval, affineBivariateX]

theorem affineBivariateY_eval (β s t x y : K) :
    bivariateEval (affineBivariateY β s t) x y = β*y+s*x+t := by
  simp [bivariateEval, affineBivariateY]

theorem affineBivariateX_totalDegree (α r : K) :
    (affineBivariateX α r).totalDegree ≤ 1 := by
  unfold affineBivariateX
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp
  · simp

theorem affineBivariateY_totalDegree (β s t : K) :
    (affineBivariateY β s t).totalDegree ≤ 1 := by
  unfold affineBivariateY
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simp
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simp
  · simp

noncomputable def affineBivariateMonomial (α r β s t : K) (a b : ℕ) :
    MvPolynomial (Fin 2) K :=
  affineBivariateX α r ^ a * affineBivariateY β s t ^ b

theorem affineBivariateMonomial_eval (α r β s t x y : K) (a b : ℕ) :
    bivariateEval (affineBivariateMonomial α r β s t a b) x y =
      (α*x+r)^a * (β*y+s*x+t)^b := by
  unfold affineBivariateMonomial
  change MvPolynomial.eval ![x,y] (_ ^ a * _ ^ b) = _
  rw [map_mul, map_pow, map_pow]
  exact congrArg₂ (· * ·)
    (congrArg (· ^ a) (affineBivariateX_eval α r x y))
    (congrArg (· ^ b) (affineBivariateY_eval β s t x y))

theorem affineBivariateMonomial_totalDegree (α r β s t : K) (a b : ℕ) :
    (affineBivariateMonomial α r β s t a b).totalDegree ≤ a+b := by
  unfold affineBivariateMonomial
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply Nat.add_le_add
  · apply (MvPolynomial.totalDegree_pow _ _).trans
    simpa using Nat.mul_le_mul_left a (affineBivariateX_totalDegree α r)
  · apply (MvPolynomial.totalDegree_pow _ _).trans
    simpa using Nat.mul_le_mul_left b (affineBivariateY_totalDegree β s t)

/-- Pull back both input pairs along the same affine coordinate map. -/
noncomputable def affineBlockPullback (α r β s t : K)
    (D : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∑ e ∈ D.support, D.coeff e • blockTensor
    (affineBivariateMonomial α r β s t (e 0) (e 1))
    (affineBivariateMonomial α r β s t (e 2) (e 3))

theorem affineBlockPullback_degree (α r β s t : K)
    {d : ℕ} (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D) :
    BlockDegreeLE d (affineBlockPullback α r β s t D) := by
  apply BlockDegreeLE_sum
  intro e he
  apply BlockDegreeLE_smul
  apply blockTensor_degree
  · exact (affineBivariateMonomial_totalDegree α r β s t (e 0) (e 1)).trans (hD e he).1
  · exact (affineBivariateMonomial_totalDegree α r β s t (e 2) (e 3)).trans (hD e he).2

theorem affineBlockPullback_eval (α r β s t : K)
    (D : MvPolynomial (Fin 4) K) (x₁ y₁ x₂ y₂ : K) :
    blockEval (affineBlockPullback α r β s t D) x₁ y₁ x₂ y₂ =
      blockEval D (α*x₁+r) (β*y₁+s*x₁+t) (α*x₂+r) (β*y₂+s*x₂+t) := by
  unfold affineBlockPullback
  simp_rw [blockEval_sum, blockEval_smul, blockTensor_eval, affineBivariateMonomial_eval]
  rw [blockEval_eq_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem BlockDegreeLE_add {d : ℕ} {D E : MvPolynomial (Fin 4) K}
    (hD : BlockDegreeLE d D) (hE : BlockDegreeLE d E) : BlockDegreeLE d (D+E) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hD e h
  · exact hE e h

theorem BlockDegreeLE_C (d : ℕ) (c : K) :
    BlockDegreeLE d (MvPolynomial.C c : MvPolynomial (Fin 4) K) := by
  apply BlockDegreeLE_monomial
  · simp
  · simp

/-- An affine change of the decoded scalar value. -/
noncomputable def affineBlockOutput (a b : K) (D : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K := a • D + MvPolynomial.C b

theorem affineBlockOutput_degree (a b : K) {d : ℕ}
    (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D) :
    BlockDegreeLE d (affineBlockOutput a b D) := by
  exact BlockDegreeLE_add (BlockDegreeLE_smul hD a) (BlockDegreeLE_C d b)

theorem affineBlockOutput_eval (a b : K)
    (D : MvPolynomial (Fin 4) K) (x₁ y₁ x₂ y₂ : K) :
    blockEval (affineBlockOutput a b D) x₁ y₁ x₂ y₂ =
      a * blockEval D x₁ y₁ x₂ y₂ + b := by
  simp [affineBlockOutput, blockEval]

end TRR08Geometry

#print axioms TRR08Geometry.affineBivariateX_eval
#print axioms TRR08Geometry.affineBivariateY_eval
#print axioms TRR08Geometry.affineBivariateX_totalDegree
#print axioms TRR08Geometry.affineBivariateY_totalDegree
#print axioms TRR08Geometry.affineBivariateMonomial_eval
#print axioms TRR08Geometry.affineBivariateMonomial_totalDegree
#print axioms TRR08Geometry.affineBlockPullback_degree
#print axioms TRR08Geometry.affineBlockPullback_eval
#print axioms TRR08Geometry.BlockDegreeLE_add
#print axioms TRR08Geometry.BlockDegreeLE_C
#print axioms TRR08Geometry.affineBlockOutput_degree
#print axioms TRR08Geometry.affineBlockOutput_eval
