import ApproximationMathlib.MultivariateTaylor

/-! Norm bounds and genuine multivariate Taylor approximation. -/
namespace MathCan.MultivariateBounds
open MathCan.MultivariateTaylor MathCan.SmoothTaylor
open Set
set_option autoImplicit false

theorem diagonal_bound {d n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n=>Space d) ℝ) (h : Space d) :
    |T (fun _=>h)|≤‖T‖*‖h‖^n := by
  simpa only [Real.norm_eq_abs,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using T.le_opNorm (fun _=>h)

theorem component_bound {d n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n=>Space d) ℝ) (w : Fin n→Fin d) :
    |T (fun r=>basis (w r))|≤‖T‖ := by
  apply le_trans _ (le_refl ‖T‖)
  simpa only [Real.norm_eq_abs] using T.unit_le_opNorm
    ((pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun r=>basis_bound (w r)))

theorem normalized_component_bound {d n : ℕ} {f : Space d→ℝ} (a : Space d) (M : ℝ)
    (hM : 0≤M) (hnorm : ‖iteratedFDeriv ℝ n f a‖≤M) (w : Fin n→Fin d) :
    |(Nat.factorial n:ℝ)⁻¹*iteratedFDeriv ℝ n f a (fun r=>basis (w r))|≤M := by
  have hp:(0:ℝ)<(Nat.factorial n:ℝ):=Nat.cast_pos.mpr (Nat.factorial_pos n)
  have h1:(1:ℝ)≤(Nat.factorial n:ℝ):=by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  rw [abs_mul,abs_inv,abs_of_pos hp,mul_comm,← div_eq_mul_inv,div_le_iff₀ hp]
  have hc:=le_trans (component_bound (iteratedFDeriv ℝ n f a) w) hnorm
  nlinarith

noncomputable def budget (d k : ℕ) : ℝ := ∑n∈Finset.range (k+1),(d:ℝ)^n

theorem budget_nonneg (d k : ℕ) : 0≤budget d k :=
  Finset.sum_nonneg (fun n _=>pow_nonneg (Nat.cast_nonneg d) n)

theorem coefficients_bound {d k : ℕ} {f : Space d→ℝ} (a : Space d) (M : ℝ) (hM : 0≤M)
    (hnorm : ∀n,n≤k → ‖iteratedFDeriv ℝ n f a‖≤M) (j : Fin (size d k)) :
    |coefficients f k a j|≤budget d k*M := by
  classical
  unfold coefficients
  calc
    _ ≤ ∑n∈Finset.range (k+1),|∑w:Fin n→Fin d,
        if counts w=labels d k j then (Nat.factorial n:ℝ)⁻¹*iteratedFDeriv ℝ n f a (fun r=>basis (w r)) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑n∈Finset.range (k+1),(d:ℝ)^n*M := by
      apply Finset.sum_le_sum
      intro n hn
      have hnk:n≤k:=by have:=Finset.mem_range.mp hn; omega
      calc
        _ ≤ ∑w:Fin n→Fin d,|if counts w=labels d k j then
            (Nat.factorial n:ℝ)⁻¹*iteratedFDeriv ℝ n f a (fun r=>basis (w r)) else 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑_w:Fin n→Fin d,M := by
          apply Finset.sum_le_sum
          intro w _
          split_ifs
          · exact normalized_component_bound a M hM (hnorm n hnk) w
          · simpa using hM
        _ = _ := by simp
    _ = _ := by simp only [budget,Finset.sum_mul]

theorem monomial_bound {d : ℕ} (beta : Fin d→ℕ) (h : Space d) (hh : ‖h‖≤1) :
    |monomial beta h|≤1 := by
  classical
  simp only [monomial,Finset.abs_prod,abs_pow]
  apply Finset.prod_le_one
  · intro j _; exact pow_nonneg (abs_nonneg _) _
  · intro j _
    exact pow_le_one₀ (abs_nonneg _) (le_trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm h j) hh)

theorem coefficient_error {d k : ℕ} (q c : Fin (size d k)→ℝ) (h : Space d) (epsilon : ℝ)
    (he : 0≤epsilon) (hh : ‖h‖≤1) (error : ∀j,|q j-c j|≤epsilon) :
    |evaluate q h-evaluate c h|≤(size d k:ℝ)*epsilon := by
  classical
  unfold evaluate
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑j:Fin (size d k),|q j*monomial (labels d k j) h-c j*monomial (labels d k j) h| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑j:Fin (size d k),|q j-c j| * |monomial (labels d k j) h| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← sub_mul,abs_mul]
    _ ≤ ∑_j:Fin (size d k),epsilon := by
      apply Finset.sum_le_sum
      intro j _
      exact le_trans (mul_le_mul_of_nonneg_right (error j) (abs_nonneg _))
        (mul_le_of_le_one_right he (monomial_bound _ h hh))
    _ = _ := by simp

theorem smooth_tensor_remainder {d n : ℕ} {f : Space d→ℝ}
    (hf : ContDiff ℝ (n+1) f) (a h : Space d) (M : ℝ) (hM : 0≤M)
    (bound : ∀t∈uIcc (0:ℝ) 1,‖iteratedFDeriv ℝ (n+1) f (a+t • h)‖≤M) :
    |f (a+h)-tensorPolynomial f n a h|≤M*‖h‖^(n+1)/(Nat.factorial (n+1):ℝ) := by
  have hg:=along_contDiff hf a h
  have hs:UniqueDiffOn ℝ (uIcc (0:ℝ) 1):=uniqueDiffOn_Icc (by norm_num)
  have hd:∀t∈uIcc (0:ℝ) 1,
      |iteratedDerivWithin (n+1) (along f a h) (uIcc (0:ℝ) 1) t|≤M*‖h‖^(n+1) := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv hs hg.contDiffAt ht,along_iteratedDeriv hf (by rfl)]
    exact le_trans (diagonal_bound _ h) (mul_le_mul_of_nonneg_right (bound t ht) (pow_nonneg (norm_nonneg h) _))
  have hr:=smooth_remainder_bound (mul_nonneg hM (pow_nonneg (norm_nonneg h) _)) hg.contDiffOn hd
  have hfn:ContDiff ℝ n f:=hf.of_le (by exact_mod_cast Nat.le_succ n)
  rw [MathCan.MultivariateTaylor.line_taylor_eq_tensor hfn a h] at hr
  simpa [along] using hr

theorem smooth_multivariate_approximation {d n : ℕ} {f : Space d→ℝ}
    (hf : ContDiff ℝ (n+1) f) (a x : Space d) (M rho epsilon : ℝ) (hM : 0≤M)
    (hdist : ‖x-a‖≤rho) (hrho : rho≤1) (he : 0≤epsilon)
    (bound : ∀t∈uIcc (0:ℝ) 1,‖iteratedFDeriv ℝ (n+1) f (a+t • (x-a))‖≤M)
    (q : Fin (size d n)→ℝ) (error : ∀j,|q j-coefficients f n a j|≤epsilon) :
    |f x-evaluate q (x-a)|≤M*rho^(n+1)/(Nat.factorial (n+1):ℝ)+(size d n:ℝ)*epsilon := by
  have ht:=smooth_tensor_remainder hf a (x-a) M hM bound
  simp only [add_sub_cancel] at ht
  have hp:=pow_le_pow_left₀ (norm_nonneg (x-a)) hdist (n+1)
  have hb:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hM) (Nat.cast_nonneg (Nat.factorial (n+1)))
  have heval:=coefficient_error q (coefficients f n a) (x-a) epsilon he (le_trans hdist hrho) error
  rw [evaluate_coefficients,abs_sub_comm] at heval
  exact le_trans (abs_sub_le (f x) (tensorPolynomial f n a (x-a)) (evaluate q (x-a)))
    (add_le_add (le_trans ht hb) heval)

end MathCan.MultivariateBounds
