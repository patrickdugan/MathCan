import Mathlib

/-!
Independent finite block transport and operator-norm stability certificates.
Motivated by the positive scalar theta composition inspected in RH26B08.
The arithmetic row spaces and analytic premises are not imported.
-/

namespace RH26E04B

open scoped BigOperators

section Exact

variable {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι]

/-- A complete resolution of the identity and annihilation of distinct blocks
    let us read each component of the forward/backward composition. -/
theorem block_scalar_projection (E : ι → V →ₗ[K] V)
    (T : V →ₗ[K] W) (P : W →ₗ[K] V) (lam : ι → K)
    (hsplit : ∀ v, (∑ j, E j v) = v)
    (hproj : ∀ i j v, E i (E j v) = if j = i then E i v else 0)
    (hblock : ∀ j v, P (T (E j v)) = lam j • E j v)
    (i : ι) (v : V) :
    E i (P (T v)) = lam i • E i v := by
  calc
    E i (P (T v)) = E i (P (T (∑ j, E j v))) :=
      congrArg (fun z => E i (P (T z))) (hsplit v).symm
    _ = ∑ j, E i (P (T (E j v))) := by simp only [map_sum]
    _ = ∑ j, if j = i then lam j • E i v else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hblock j v, map_smul, hproj i j v]
      split_ifs <;> simp
    _ = lam i • E i v := by simp

theorem block_scalar_recovery (E : ι → V →ₗ[K] V)
    (T : V →ₗ[K] W) (P : W →ₗ[K] V) (lam : ι → K)
    (hsplit : ∀ v, (∑ j, E j v) = v)
    (hproj : ∀ i j v, E i (E j v) = if j = i then E i v else 0)
    (hblock : ∀ j v, P (T (E j v)) = lam j • E j v)
    (hnz : ∀ j, lam j ≠ 0) (v : V) :
    (∑ j, (lam j)⁻¹ • E j (P (T v))) = v := by
  calc
    _ = ∑ j, E j v := by
      apply Finset.sum_congr rfl
      intro j _
      rw [block_scalar_projection E T P lam hsplit hproj hblock j v,
        smul_smul, inv_mul_cancel₀ (hnz j), one_smul]
    _ = v := hsplit v

theorem block_scalar_injective (E : ι → V →ₗ[K] V)
    (T : V →ₗ[K] W) (P : W →ₗ[K] V) (lam : ι → K)
    (hsplit : ∀ v, (∑ j, E j v) = v)
    (hproj : ∀ i j v, E i (E j v) = if j = i then E i v else 0)
    (hblock : ∀ j v, P (T (E j v)) = lam j • E j v)
    (hnz : ∀ j, lam j ≠ 0) : Function.Injective T := by
  intro u v huv
  have hu := block_scalar_recovery E T P lam hsplit hproj hblock hnz u
  have hv := block_scalar_recovery E T P lam hsplit hproj hblock hnz v
  rw [huv] at hu
  exact hu.symm.trans hv

end Exact

section Energy

variable {ι : Type*} [Fintype ι]

/-- Weighted squared energies with a common nonnegative lower gain. -/
theorem finite_energy_bound (r g : ι → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hg : ∀ i, a ≤ g i) :
    a ^ 2 * (∑ i, (r i) ^ 2) ≤ ∑ i, (g i * r i) ^ 2 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hgg : 0 ≤ g i := ha.trans (hg i)
  have hsq : a ^ 2 ≤ (g i) ^ 2 := by
    simpa only [pow_two] using mul_le_mul (hg i) (hg i) ha hgg
  calc
    _ ≤ (g i) ^ 2 * (r i) ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg (r i))
    _ = _ := by ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The orthogonal/Pythagorean energy identity is an explicit premise.
    No norm identity is inferred from algebraic directness alone. -/
theorem orthogonal_block_gain (E : ι → V →L[ℝ] V)
    (A : V →L[ℝ] V) (lam : ι → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hg : ∀ i, a ≤ ‖lam i‖)
    (henergy : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖E i v‖ ^ 2)
    (hscalar : ∀ i v, E i (A v) = lam i • E i v) (v : V) :
    a * ‖v‖ ≤ ‖A v‖ := by
  classical
  have hsq : (a * ‖v‖) ^ 2 ≤ ‖A v‖ ^ 2 := by
    calc
      _ = a ^ 2 * ‖v‖ ^ 2 := by ring
      _ = a ^ 2 * (∑ i, ‖E i v‖ ^ 2) := by rw [henergy v]
      _ ≤ ∑ i, (‖lam i‖ * ‖E i v‖) ^ 2 :=
        finite_energy_bound (fun i => ‖E i v‖) (fun i => ‖lam i‖) a ha hg
      _ = ‖A v‖ ^ 2 := by
        rw [henergy (A v)]
        apply Finset.sum_congr rfl
        intro i _
        rw [hscalar i v, norm_smul]
  by_contra! hn
  have hp : 0 < a * ‖v‖ - ‖A v‖ := sub_pos.mpr hn
  have hq : 0 < a * ‖v‖ + ‖A v‖ :=
    add_pos_of_pos_of_nonneg ((norm_nonneg (A v)).trans_lt hn) (norm_nonneg _)
  have hh := mul_pos hp hq
  have he : (a * ‖v‖ - ‖A v‖) * (a * ‖v‖ + ‖A v‖) =
      (a * ‖v‖) ^ 2 - ‖A v‖ ^ 2 := by ring
  rw [he] at hh
  exact (not_lt_of_ge hsq) (sub_pos.mp hh)

end Energy

section Stability

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem perturbed_composition_gain (T : V →L[ℝ] W)
    (P : W →L[ℝ] V) (A : V →L[ℝ] V) (a delta : ℝ)
    (hA : ∀ v, a * ‖v‖ ≤ ‖A v‖)
    (hres : ‖P.comp T - A‖ ≤ delta) (v : V) :
    (a - delta) * ‖v‖ ≤ ‖P (T v)‖ := by
  have hr : ‖P (T v) - A v‖ ≤ delta * ‖v‖ := by
    have he := (P.comp T - A).le_opNorm v
    have he' : ‖P (T v) - A v‖ ≤ ‖P.comp T - A‖ * ‖v‖ := by
      simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply] using he
    exact he'.trans (mul_le_mul_of_nonneg_right hres (norm_nonneg v))
  have htri : ‖A v‖ ≤ ‖P (T v)‖ + ‖P (T v) - A v‖ := by
    calc
      _ = ‖P (T v) - (P (T v) - A v)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_sub_le _ _
  calc
    _ = a * ‖v‖ - delta * ‖v‖ := by ring
    _ ≤ ‖A v‖ - delta * ‖v‖ := sub_le_sub_right (hA v) _
    _ ≤ ‖P (T v)‖ := by linarith only [hr, htri]

theorem forward_gain (T : V →L[ℝ] W)
    (P : W →L[ℝ] V) (A : V →L[ℝ] V) (a delta : ℝ)
    (hA : ∀ v, a * ‖v‖ ≤ ‖A v‖)
    (hres : ‖P.comp T - A‖ ≤ delta) (hP : 0 < ‖P‖) (v : V) :
    ((a - delta) / ‖P‖) * ‖v‖ ≤ ‖T v‖ := by
  have hh := (perturbed_composition_gain T P A a delta hA hres v).trans (P.le_opNorm (T v))
  calc
    _ = ((a - delta) * ‖v‖) / ‖P‖ := by ring
    _ ≤ ‖T v‖ := (div_le_iff₀ hP).2 (by simpa only [mul_comm ‖P‖] using hh)

theorem perturbed_injective (T : V →L[ℝ] W)
    (P : W →L[ℝ] V) (A : V →L[ℝ] V) (a delta : ℝ)
    (hA : ∀ v, a * ‖v‖ ≤ ‖A v‖)
    (hres : ‖P.comp T - A‖ ≤ delta) (hgap : delta < a) :
    Function.Injective T := by
  intro u v huv
  have hz : T (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hh := perturbed_composition_gain T P A a delta hA hres (u - v)
  rw [hz, map_zero, norm_zero] at hh
  by_contra hn
  have hdiff : u - v ≠ 0 := fun h => hn (sub_eq_zero.mp h)
  have hv : 0 < ‖u - v‖ := norm_pos_iff.mpr hdiff
  exact (not_lt_of_ge hh) (mul_pos (sub_pos.mpr hgap) hv)

end Stability

section Conditioning

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem conditioned_block_gain (A D S Sinv : V →L[ℝ] V) (a : ℝ)
    (ha : 0 ≤ a) (hD : ∀ v, a * ‖v‖ ≤ ‖D v‖)
    (hInv : ∀ v, S (Sinv v) = v)
    (hconj : ∀ v, Sinv (A v) = D (Sinv v))
    (hS : 0 < ‖S‖) (hSi : 0 < ‖Sinv‖) (v : V) :
    (a / (‖S‖ * ‖Sinv‖)) * ‖v‖ ≤ ‖A v‖ := by
  have hcoord : ‖v‖ ≤ ‖S‖ * ‖Sinv v‖ := by
    calc
      ‖v‖ = ‖S (Sinv v)‖ := congrArg norm (hInv v).symm
      _ ≤ _ := S.le_opNorm (Sinv v)
  have hdiag : a * ‖Sinv v‖ ≤ ‖Sinv (A v)‖ := by
    rw [hconj v]
    exact hD (Sinv v)
  have hh : a * ‖v‖ ≤ ‖A v‖ * (‖S‖ * ‖Sinv‖) := by
    calc
      _ ≤ a * (‖S‖ * ‖Sinv v‖) := mul_le_mul_of_nonneg_left hcoord ha
      _ = ‖S‖ * (a * ‖Sinv v‖) := by ring
      _ ≤ ‖S‖ * ‖Sinv (A v)‖ := mul_le_mul_of_nonneg_left hdiag hS.le
      _ ≤ ‖S‖ * (‖Sinv‖ * ‖A v‖) :=
        mul_le_mul_of_nonneg_left (Sinv.le_opNorm (A v)) hS.le
      _ = _ := by ring
  calc
    _ = (a * ‖v‖) / (‖S‖ * ‖Sinv‖) := by ring
    _ ≤ ‖A v‖ := (div_le_iff₀ (mul_pos hS hSi)).2 hh

end Conditioning

theorem zero_gain_control :
    ∃ (T P : ℚ →ₗ[ℚ] ℚ), (∀ v, P (T v) = (0 : ℚ) • v) ∧
      ¬ Function.Injective T := by
  refine ⟨0, LinearMap.id, ?_, ?_⟩
  · intro v
    simp
  · intro hi
    have h : (0 : ℚ) = 1 := hi (by simp)
    norm_num at h

/-- A cancellation at the threshold on a one-dimensional real space. -/
theorem threshold_equality_control :
    ∃ (T P A : ℝ →L[ℝ] ℝ),
      (∀ v, (1 / 2 : ℝ) * ‖v‖ ≤ ‖A v‖) ∧
      ‖P.comp T - A‖ = (1 / 2 : ℝ) ∧ ¬ Function.Injective T := by
  let T : ℝ →L[ℝ] ℝ := 0
  let P : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
  let A : ℝ →L[ℝ] ℝ := (1 / 2 : ℝ) • P
  have hPn : ‖P‖ = 1 := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound P (by norm_num)
      intro v
      change ‖v‖ ≤ 1 * ‖v‖
      simp
    · have h := P.le_opNorm (1 : ℝ)
      change ‖(1 : ℝ)‖ ≤ ‖P‖ * ‖(1 : ℝ)‖ at h
      simpa using h
  refine ⟨T, P, A, ?_, ?_, ?_⟩
  · intro v
    change (1 / 2 : ℝ) * ‖v‖ ≤ ‖(1 / 2 : ℝ) • v‖
    rw [norm_smul]
    norm_num [Real.norm_eq_abs]
  · have he : P.comp T - A = -A := by
      ext v
      simp [T]
    rw [he, norm_neg]
    change ‖(1 / 2 : ℝ) • P‖ = (1 / 2 : ℝ)
    rw [norm_smul, hPn]
    norm_num [Real.norm_eq_abs]
  · intro hi
    have h : (0 : ℝ) = 1 := hi (by simp [T])
    norm_num at h

end RH26E04B

#print axioms RH26E04B.block_scalar_projection
#print axioms RH26E04B.block_scalar_recovery
#print axioms RH26E04B.block_scalar_injective
#print axioms RH26E04B.finite_energy_bound
#print axioms RH26E04B.orthogonal_block_gain
#print axioms RH26E04B.perturbed_composition_gain
#print axioms RH26E04B.forward_gain
#print axioms RH26E04B.perturbed_injective
#print axioms RH26E04B.conditioned_block_gain
#print axioms RH26E04B.zero_gain_control
#print axioms RH26E04B.threshold_equality_control
