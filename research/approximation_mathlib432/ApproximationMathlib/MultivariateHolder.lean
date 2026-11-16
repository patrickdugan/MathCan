import ApproximationMathlib.MultivariateBounds

/-! Fractional smoothness for the genuine multivariate tensor polynomial. -/
namespace MathCan.MultivariateHolder
open MathCan.MultivariateTaylor MathCan.MultivariateBounds MathCan.SmoothTaylor
open Set
set_option autoImplicit false

theorem holder_tensor_remainder {d n : ℕ} {f : Space d→ℝ}
    (hf : ContDiff ℝ (n+1) f) (a h : Space d) (H alpha : ℝ) (hH : 0≤H) (ha : 0≤alpha)
    (holder : ∀t∈uIcc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ (n+1) f (a+t • h)-iteratedFDeriv ℝ (n+1) f a‖≤H*‖a+t • h-a‖^alpha) :
    |f (a+h)-tensorPolynomial f (n+1) a h|≤
      H*‖h‖^(((n+1:ℕ):ℝ)+alpha)/(Nat.factorial (n+1):ℝ) := by
  have hg:=along_contDiff hf a h
  have hs:UniqueDiffOn ℝ (uIcc (0:ℝ) 1):=uniqueDiffOn_Icc (by norm_num)
  have hd:∀t∈uIcc (0:ℝ) 1,
      |iteratedDerivWithin (n+1) (along f a h) (uIcc (0:ℝ) 1) t-
        iteratedDerivWithin (n+1) (along f a h) (uIcc (0:ℝ) 1) 0|≤
        (H*‖h‖^(((n+1:ℕ):ℝ)+alpha))*|t-0|^alpha := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv hs hg.contDiffAt ht,
      iteratedDerivWithin_eq_iteratedDeriv hs hg.contDiffAt left_mem_uIcc,
      along_iteratedDeriv hf (by rfl),along_iteratedDeriv hf (by rfl)]
    simp only [zero_smul,add_zero,sub_zero]
    have hdiag:=diagonal_bound (iteratedFDeriv ℝ (n+1) f (a+t • h)-iteratedFDeriv ℝ (n+1) f a) h
    simp only [ContinuousMultilinearMap.sub_apply] at hdiag
    calc
      _ ≤ ‖iteratedFDeriv ℝ (n+1) f (a+t • h)-iteratedFDeriv ℝ (n+1) f a‖*‖h‖^(n+1) := hdiag
      _ ≤ (H*‖a+t • h-a‖^alpha)*‖h‖^(n+1) :=
        mul_le_mul_of_nonneg_right (holder t ht) (pow_nonneg (norm_nonneg h) _)
      _ = _ := by
        simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
        rw [Real.mul_rpow (abs_nonneg t) (norm_nonneg h),
          Real.rpow_add_of_nonneg (norm_nonneg h) (Nat.cast_nonneg _) ha,Real.rpow_natCast]
        ring
  have hr:=holder_remainder_bound (mul_nonneg hH (Real.rpow_nonneg (norm_nonneg h) _)) ha hg.contDiffOn hd
  rw [line_taylor_eq_tensor hf a h] at hr
  simpa [along] using hr

theorem holder_multivariate_approximation {d n : ℕ} {f : Space d→ℝ}
    (hf : ContDiff ℝ (n+1) f) (a x : Space d) (H alpha rho epsilon : ℝ)
    (hH : 0≤H) (ha : 0≤alpha) (hdist : ‖x-a‖≤rho) (hrho : rho≤1) (he : 0≤epsilon)
    (holder : ∀t∈uIcc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ (n+1) f (a+t • (x-a))-iteratedFDeriv ℝ (n+1) f a‖≤H*‖a+t • (x-a)-a‖^alpha)
    (q : Fin (size d (n+1))→ℝ) (error : ∀j,|q j-coefficients f (n+1) a j|≤epsilon) :
    |f x-evaluate q (x-a)|≤
      H*rho^(((n+1:ℕ):ℝ)+alpha)/(Nat.factorial (n+1):ℝ)+(size d (n+1):ℝ)*epsilon := by
  have ht:=holder_tensor_remainder hf a (x-a) H alpha hH ha holder
  simp only [add_sub_cancel] at ht
  have hp:=Real.rpow_le_rpow (norm_nonneg (x-a)) hdist
    (show 0≤((n+1:ℕ):ℝ)+alpha by positivity)
  have hb:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hH) (Nat.cast_nonneg (Nat.factorial (n+1)))
  have heval:=coefficient_error q (coefficients f (n+1) a) (x-a) epsilon he (le_trans hdist hrho) error
  rw [evaluate_coefficients,abs_sub_comm] at heval
  exact le_trans (abs_sub_le (f x) (tensorPolynomial f (n+1) a (x-a)) (evaluate q (x-a)))
    (add_le_add (le_trans ht hb) heval)

end MathCan.MultivariateHolder
