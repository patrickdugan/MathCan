import ApproximationMathlib.TaylorFoundation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Analytic Taylor remainders derived from smoothness, with explicit constants.
The within-interval derivatives handle boundary points of the domain. -/
namespace MathCan.SmoothTaylor
open Set
open scoped Interval Nat
open MathCan.TaylorFoundation

/-- The degree-zero case covers Hölder functions below one derivative. -/
theorem holder_zero_remainder {f : ℝ → ℝ} {a x H alpha : ℝ}
    (holder:∀c∈uIcc a x,|f c-f a|≤H*|c-a|^alpha) :
    |f x-taylorWithinEval f 0 (uIcc a x) a x|≤H*|x-a|^alpha := by
  simpa only [taylor_within_zero_eval] using holder x right_mem_uIcc

/-- An actual Lagrange remainder with a uniform derivative bound. -/
theorem remainder_bound {f : ℝ → ℝ} {a x M : ℝ} {n : ℕ}
    (hM:0≤M) (hf:ContDiffOn ℝ n f (uIcc a x))
    (hd:DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc a x)) (uIoo a x))
    (bound:∀ c∈uIcc a x, |iteratedDerivWithin (n+1) f (uIcc a x) c|≤M) :
    |f x-taylorWithinEval f n (uIcc a x) a x|≤M*|x-a|^(n+1)/(n+1)! := by
  by_cases he:a=x
  · subst x
    simp [taylorWithinEval_self]
  · obtain ⟨c,hc,hr⟩:=taylor_mean_remainder_lagrange he hf hd
    have hfact:(0:ℝ)<((n+1)!:ℝ):=Nat.cast_pos.mpr (Nat.factorial_pos _)
    rw [hr,abs_div,abs_mul,abs_pow,abs_of_pos hfact]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (bound c (uIoo_subset_uIcc_self hc)) (pow_nonneg (abs_nonneg _) _))
      (Nat.cast_nonneg _)

/-- The differentiability premise is supplied by C^(n+1) regularity. -/
theorem smooth_remainder_bound {f : ℝ → ℝ} {a x M : ℝ} {n : ℕ}
    (hM:0≤M) (hf:ContDiffOn ℝ (n+1) f (uIcc a x))
    (bound:∀ c∈uIcc a x, |iteratedDerivWithin (n+1) f (uIcc a x) c|≤M) :
    |f x-taylorWithinEval f n (uIcc a x) a x|≤M*|x-a|^(n+1)/(n+1)! := by
  by_cases he:a=x
  · subst x
    simp [taylorWithinEval_self]
  · have hu:UniqueDiffOn ℝ (uIcc a x):=uniqueDiffOn_Icc (by grind)
    have hd:DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc a x)) (uIcc a x) := by
      apply hf.differentiableOn_iteratedDerivWithin _ hu
      norm_cast
      simp
    exact remainder_bound hM hf.of_succ (hd.mono Ioo_subset_Icc_self) bound

/-- Subtracting the top coefficient turns a lower-order mean remainder into
an oscillation of the highest derivative. -/
theorem remainder_top_oscillation {f : ℝ → ℝ} {a x : ℝ} {n : ℕ}
    (he:a≠x) (hf:ContDiffOn ℝ (n+1) f (uIcc a x)) :
    ∃c∈uIoo a x,
      f x-taylorWithinEval f (n+1) (uIcc a x) a x =
      (iteratedDerivWithin (n+1) f (uIcc a x) c-
        iteratedDerivWithin (n+1) f (uIcc a x) a)*(x-a)^(n+1)/(n+1)! := by
  have hu:UniqueDiffOn ℝ (uIcc a x):=uniqueDiffOn_Icc (by grind)
  have hd:DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc a x)) (uIcc a x) := by
    apply hf.differentiableOn_iteratedDerivWithin _ hu
    norm_cast
    simp
  obtain ⟨c,hc,hr⟩:=taylor_mean_remainder_lagrange he hf.of_succ (hd.mono Ioo_subset_Icc_self)
  refine ⟨c,hc,?_⟩
  rw [taylorWithinEval_succ]
  simp only [smul_eq_mul]
  rw [sub_add_eq_sub_sub,hr,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  ring

/-- C^(n+1,alpha) regularity gives the fractional Taylor rate, including at
zero displacement, for every nonnegative Hölder exponent. -/
theorem holder_remainder_bound {f : ℝ → ℝ} {a x H alpha : ℝ} {n : ℕ}
    (hH:0≤H) (ha:0≤alpha) (hf:ContDiffOn ℝ (n+1) f (uIcc a x))
    (holder:∀c∈uIcc a x,
      |iteratedDerivWithin (n+1) f (uIcc a x) c-
        iteratedDerivWithin (n+1) f (uIcc a x) a|≤H*|c-a|^alpha) :
    |f x-taylorWithinEval f (n+1) (uIcc a x) a x|≤
      H*|x-a|^(((n+1:ℕ):ℝ)+alpha)/(n+1)! := by
  by_cases he:a=x
  · subst x
    rw [taylorWithinEval_self,sub_self,abs_zero]
    exact div_nonneg (mul_nonneg hH (Real.rpow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _)
  · obtain ⟨c,hc,hr⟩:=remainder_top_oscillation he hf
    have hdist:|c-a|≤|x-a|:=abs_sub_left_of_mem_uIcc (uIoo_subset_uIcc_self hc)
    have hp:=Real.rpow_le_rpow (abs_nonneg (c-a)) hdist ha
    have htop:=le_trans (holder c (uIoo_subset_uIcc_self hc)) (mul_le_mul_of_nonneg_left hp hH)
    have hbound:=mul_le_mul_of_nonneg_right htop (pow_nonneg (abs_nonneg (x-a)) (n+1))
    have hfact:(0:ℝ)<((n+1)!:ℝ):=Nat.cast_pos.mpr (Nat.factorial_pos _)
    rw [hr,abs_div,abs_mul,abs_pow,abs_of_pos hfact]
    calc
      _ ≤ (H*|x-a|^alpha)*|x-a|^(n+1)/(n+1)! := div_le_div_of_nonneg_right hbound (Nat.cast_nonneg _)
      _ = _ := by
        rw [Real.rpow_add_of_nonneg (abs_nonneg _) (Nat.cast_nonneg _) ha,Real.rpow_natCast]
        ring

/-- The analytic remainder is compatible with the normalized transport scale.
A dyadic choice with mu^s ≤ 2*tau gives a correction budget independent of mu. -/
theorem scaled_holder_remainder {f : ℝ → ℝ} {a mu q tau D H alpha : ℝ} {n : ℕ}
    (hmu:0≤mu) (htau:0<tau) (hD:0≤D) (hq:|q|≤D) (hH:0≤H) (ha:0≤alpha)
    (hscale:mu^(((n+1:ℕ):ℝ)+alpha)≤2*tau)
    (hf:ContDiffOn ℝ (n+1) f (uIcc a (a+mu*q)))
    (holder:∀c∈uIcc a (a+mu*q),
      |iteratedDerivWithin (n+1) f (uIcc a (a+mu*q)) c-
        iteratedDerivWithin (n+1) f (uIcc a (a+mu*q)) a|≤H*|c-a|^alpha) :
    |f (a+mu*q)-taylorWithinEval f (n+1) (uIcc a (a+mu*q)) a (a+mu*q)|/tau≤
      2*H*D^(((n+1:ℕ):ℝ)+alpha)/(n+1)! := by
  let s:ℝ:=((n+1:ℕ):ℝ)+alpha
  have hs:0≤s:=by dsimp [s]; positivity
  have hr:=holder_remainder_bound hH ha hf holder
  have hdist:|a+mu*q-a|≤mu*D:=by
    simpa only [add_sub_cancel_left,abs_mul,abs_of_nonneg hmu] using mul_le_mul_of_nonneg_left hq hmu
  have hp:=Real.rpow_le_rpow (abs_nonneg (a+mu*q-a)) hdist hs
  have hm: H*|a+mu*q-a|^s≤H*(mu*D)^s:=mul_le_mul_of_nonneg_left hp hH
  rw [Real.mul_rpow hmu hD] at hm
  have hn:0≤H*D^s:=mul_nonneg hH (Real.rpow_nonneg hD _)
  have hb:=mul_le_mul_of_nonneg_right hscale hn
  have hfpos:(0:ℝ)<(n+1)!:=Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hfnon:0≤((n+1)!:ℝ):=le_of_lt hfpos
  calc
    _ ≤ (H*|a+mu*q-a|^s/(n+1)!)/tau := div_le_div_of_nonneg_right hr (le_of_lt htau)
    _ ≤ (H*(mu^s*D^s)/(n+1)!)/tau :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hm hfnon) (le_of_lt htau)
    _ ≤ (2*tau*(H*D^s)/(n+1)!)/tau := by
      apply div_le_div_of_nonneg_right _ (le_of_lt htau)
      apply div_le_div_of_nonneg_right _ hfnon
      nlinarith [hb]
    _ = _ := by field_simp; ring

end MathCan.SmoothTaylor
