import Mathlib

/-!
Independent small-prime and joint conductor supplier certificates.
The component arithmetic inequalities and source realization remain explicit
premises (RH26B10, RH26B13, RH26B14).
-/

namespace RH26E05C2

open scoped BigOperators

noncomputable def smallPoly (C : ℝ) : ℝ :=
  C + 11*C*(3+2*C) + 80*C + 64*C + 32*C +
    4*C*(102+4*(2*C+1)^2)

theorem small_polynomial_expand (C : ℝ) :
    smallPoly C = 64*C^3 + 86*C^2 + 634*C := by
  unfold smallPoly
  ring

theorem small_gap_identity (C : ℝ) :
    104*(C+1)^3 - smallPoly C =
      40*(C-3/5)^2*(C+6/5) + 226*(C-697/1130)^2 + 4159/5650 := by
  unfold smallPoly
  ring

theorem small_envelope (C : ℝ) (hC : 0 ≤ C) :
    smallPoly C ≤ 104*(C+1)^3 := by
  have h1 : 0 ≤ 40*(C-3/5)^2*(C+6/5) := by positivity
  have h2 : 0 ≤ 226*(C-697/1130)^2 := by positivity
  linarith only [small_gap_identity C, h1, h2]

theorem small_integer_minimum (K : ℕ) :
    (∀ C : ℝ, 0 ≤ C → smallPoly C ≤ (K : ℝ)*(C+1)^3) ↔
      104 ≤ K := by
  constructor
  · intro h
    by_contra hn
    have hk : K ≤ 103 := by omega
    have hk' : (K : ℝ) ≤ 103 := by exact_mod_cast hk
    have ht := h (3/5) (by norm_num)
    norm_num [smallPoly] at ht
    linarith only [ht, hk']
  · intro hk C hC
    have hk' : (104 : ℝ) ≤ K := by exact_mod_cast hk
    exact (small_envelope C hC).trans
      (mul_le_mul_of_nonneg_right hk' (pow_nonneg (by linarith) 3))

theorem small_assembly (C X Y bb ep rb rc rd fl : ℝ)
    (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hY : Y ≤ bb+ep+rb+rc+rd+fl)
    (hb : bb ≤ C*X) (he : ep ≤ 11*C*(3+2*C)*X)
    (hrb : rb ≤ 80*C*X) (hrc : rc ≤ 64*C*X)
    (hrd : rd ≤ 32*C*X)
    (hf : fl ≤ 4*C*(102+4*(2*C+1)^2)*X) :
    Y ≤ 104*(C+1)^3*X := by
  have hp : Y ≤ smallPoly C * X := by
    unfold smallPoly
    linarith only [hY, hb, he, hrb, hrc, hrd, hf]
  exact hp.trans (mul_le_mul_of_nonneg_right (small_envelope C hC) hX)

/-- The exact two-term assembly from the source small-prime row estimate.
    The prime-factor logarithm budget is supplied as hlog. -/
theorem row23_assembly {I : Type*} (T : Finset I) (w : I → ℝ)
    (C fm b y A g : ℝ) (hC : 0 ≤ C) (hy : 0 ≤ y)
    (hA : 0 ≤ A) (hfm : 1 ≤ fm) (hg : 1 ≤ g)
    (hLg : (C+3)^2*(1+y)^2 ≤ g) (hb : A*g ≤ b)
    (hlog : (∑ i ∈ T, w i) ≤ 2*C*y+2) :
    (∑ i ∈ T, w i*(C*fm*b*y+C*A*g^2)) ≤ 2*C*fm*b*g^2 := by
  let B : ℝ := 2*C*y+2
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hY0 : 0 ≤ 1+y := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hf0 : 0 ≤ fm := by linarith
  have hb0 : 0 ≤ b := (mul_nonneg hA hg0).trans hb
  have hB1 : B ≤ (2*C+2)*(1+y) := by
    dsimp [B]
    nlinarith only [hy, hC]
  have hC2 : 2*C+2 ≤ (C+3)^2 := by
    nlinarith only [hC, sq_nonneg C]
  have hBprod : B*(1+y) ≤ g := by
    calc
      _ ≤ ((2*C+2)*(1+y))*(1+y) :=
        mul_le_mul_of_nonneg_right hB1 hY0
      _ = (2*C+2)*(1+y)^2 := by ring
      _ ≤ (C+3)^2*(1+y)^2 :=
        mul_le_mul_of_nonneg_right hC2 (sq_nonneg _)
      _ ≤ _ := hLg
  have hBg : B ≤ g :=
    (le_mul_of_one_le_right hB0 (by linarith)).trans hBprod
  have hBy : B*y ≤ g^2 := by
    calc
      _ ≤ B*(1+y) := mul_le_mul_of_nonneg_left (by linarith) hB0
      _ ≤ g := hBprod
      _ ≤ g^2 := by nlinarith only [hg, mul_nonneg hg0 (sub_nonneg.mpr hg)]
  have hBA : B*A ≤ b := by
    calc
      _ ≤ g*A := mul_le_mul_of_nonneg_right hBg hA
      _ = A*g := mul_comm _ _
      _ ≤ _ := hb
  have hcfb : 0 ≤ C*fm*b := mul_nonneg (mul_nonneg hC hf0) hb0
  have hcost : 0 ≤ C*fm*b*y+C*A*g^2 := by positivity
  have hlog' : (∑ i ∈ T, w i) ≤ B := hlog
  have ht1 : C*fm*b*(B*y) ≤ C*fm*b*g^2 :=
    mul_le_mul_of_nonneg_left hBy hcfb
  have ht2 : C*g^2*(B*A) ≤ C*fm*b*g^2 := by
    calc
      _ ≤ C*g^2*b := mul_le_mul_of_nonneg_left hBA (by positivity)
      _ ≤ C*g^2*(fm*b) := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left hb0 hfm) (by positivity)
      _ = _ := by ring
  calc
    _ = (∑ i ∈ T, w i)*(C*fm*b*y+C*A*g^2) := by rw [Finset.sum_mul]
    _ ≤ B*(C*fm*b*y+C*A*g^2) := mul_le_mul_of_nonneg_right hlog' hcost
    _ = C*fm*b*(B*y)+C*g^2*(B*A) := by ring
    _ ≤ C*fm*b*g^2+C*fm*b*g^2 := add_le_add ht1 ht2
    _ = _ := by ring

/-- Keep the actual conductor powers when taking logarithms. -/
theorem conductor_log_budget (Q q d t b g : ℝ)
    (hQ : 1 ≤ Q) (hq : 1 ≤ q) (hd : 1 ≤ d)
    (ht : 1 ≤ t) (hb : 1 ≤ b)
    (hcond : (Q*q*d)^36*t^150 ≤ b^(1/2 : ℝ))
    (hlog : Real.log b = g) :
    36*(Real.log Q+Real.log q+Real.log d)+150*Real.log t ≤ g/2 := by
  have hQ0 : 0 < Q := by linarith
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < d := by linarith
  have ht0 : 0 < t := by linarith
  have hb0 : 0 < b := by linarith
  have hP : 0 < Q*q*d := by positivity
  have hp : 0 < (Q*q*d)^36*t^150 := by positivity
  have h := Real.log_le_log hp hcond
  rw [Real.log_mul (pow_ne_zero _ hP.ne') (pow_ne_zero _ ht0.ne')] at h
  simp only [Real.log_pow, Real.log_rpow hb0,
    Real.log_mul (mul_ne_zero hQ0.ne' hq0.ne') hd0.ne',
    Real.log_mul hQ0.ne' hq0.ne', hlog] at h
  push_cast at h
  linarith only [h]

theorem conductor_pair_budget (Q q d t b g : ℝ)
    (hQ : 1 ≤ Q) (hq : 1 ≤ q) (hd : 1 ≤ d)
    (ht : 1 ≤ t) (hb : 1 ≤ b)
    (hcond : (Q*q*d)^36*t^150 ≤ b^(1/2 : ℝ))
    (hlog : Real.log b = g) :
    Real.log q+Real.log d ≤ g/72-Real.log Q-(25/6)*Real.log t ∧
    g/72-Real.log Q-(25/6)*Real.log t ≤ g/72 := by
  have h := conductor_log_budget Q q d t b g hQ hq hd ht hb hcond hlog
  have hQ' := Real.log_nonneg hQ
  have ht' := Real.log_nonneg ht
  exact ⟨by linarith only [h], by linarith only [hQ', ht']⟩

theorem pair_support_log_bound (T : Finset ℕ) (q d : ℕ)
    (hT : ∀ l ∈ T, l=q ∨ l=d) :
    (∑ l ∈ T, Real.log (l : ℝ)) ≤ Real.log (q : ℝ)+Real.log (d : ℝ) := by
  classical
  have hsub : T ⊆ ({q,d} : Finset ℕ) := by
    intro l hl
    rcases hT l hl with h | h <;> simp [h]
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun l _ _ => Real.log_natCast_nonneg l)
  by_cases hqd : q=d
  · subst d
    simp at hsum
    linarith only [hsum, Real.log_natCast_nonneg q]
  · rw [Finset.sum_insert (by simpa using hqd), Finset.sum_singleton] at hsum
    exact hsum

theorem ramified_assembly (T : Finset ℕ) (q d : ℕ)
    (Q t b g C fm : ℝ) (hQ : 1 ≤ Q) (hq : 1 ≤ q) (hd : 1 ≤ d)
    (ht : 1 ≤ t) (hb : 1 ≤ b) (hg : 1 ≤ g)
    (hC : 0 ≤ C) (hfm : 0 ≤ fm)
    (hcond : (Q*(q : ℝ)*(d : ℝ))^36*t^150 ≤ b^(1/2 : ℝ))
    (hlog : Real.log b = g) (hT : ∀ l ∈ T, l=q ∨ l=d) :
    (∑ l ∈ T, Real.log (l : ℝ)*(2*C*fm*b)) ≤ (C/36)*fm*b*g ∧
    (C/36)*fm*b*g ≤ (C/36)*fm*b*g^2 := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp := conductor_pair_budget Q q d t b g hQ hq' hd' ht hb hcond hlog
  have hs := (pair_support_log_bound T q d hT).trans (hp.1.trans hp.2)
  have hcost : 0 ≤ 2*C*fm*b := by positivity
  have hg0 : 0 ≤ g := by linarith
  have hgg : g ≤ g^2 := by nlinarith only [hg, mul_nonneg hg0 (sub_nonneg.mpr hg)]
  refine ⟨?_, ?_⟩
  · calc
      _ = (∑ l ∈ T, Real.log (l : ℝ))*(2*C*fm*b) := by rw [Finset.sum_mul]
      _ ≤ (g/72)*(2*C*fm*b) := mul_le_mul_of_nonneg_right hs hcost
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_left hgg (by positivity)

theorem conductor_sharp_fixture (g : ℝ) (hg : 0 < g) :
    ∃ Q q d t b : ℝ, Q=1 ∧ q=Real.exp (g/72) ∧ d=1 ∧ t=1 ∧ b=Real.exp g ∧
      1 ≤ Q ∧ 1 ≤ q ∧ 1 ≤ d ∧ 1 ≤ t ∧ 1 ≤ b ∧
      (Q*q*d)^36*t^150 = b^(1/2 : ℝ) ∧ Real.log q+Real.log d=g/72 := by
  have hq : 1 ≤ Real.exp (g/72) := Real.one_le_exp (by positivity)
  have hb : 1 ≤ Real.exp g := Real.one_le_exp hg.le
  have hpow : (Real.exp (g/72))^36 = (Real.exp g)^(1/2 : ℝ) := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos (Real.exp_pos g), Real.log_exp]
    congr 1
    <;> ring
  refine ⟨1, Real.exp (g/72), 1, 1, Real.exp g,
    rfl, rfl, rfl, rfl, rfl, le_rfl, hq, le_rfl, le_rfl, hb, ?_, ?_⟩
  · simpa using hpow
  · simp

theorem missing_conductor_factor_control :
    ∃ Q q d t b : ℝ, 0 < Q ∧ Q < 1 ∧
      1 ≤ q ∧ 1 ≤ d ∧ 1 ≤ t ∧ 1 ≤ b ∧
      (Q*q*d)^36*t^150 ≤ b^(1/2 : ℝ) ∧
      Real.log b/72 < Real.log q+Real.log d := by
  refine ⟨1/2, 2, 1, 1, 1, by norm_num, by norm_num,
    by norm_num, le_rfl, le_rfl, le_rfl, ?_, ?_⟩
  · norm_num
  · simpa using Real.log_pos (show (1 : ℝ) < 2 by norm_num)

end RH26E05C2

#print axioms RH26E05C2.small_polynomial_expand
#print axioms RH26E05C2.small_gap_identity
#print axioms RH26E05C2.small_envelope
#print axioms RH26E05C2.small_integer_minimum
#print axioms RH26E05C2.small_assembly
#print axioms RH26E05C2.row23_assembly
#print axioms RH26E05C2.conductor_log_budget
#print axioms RH26E05C2.conductor_pair_budget
#print axioms RH26E05C2.pair_support_log_bound
#print axioms RH26E05C2.ramified_assembly
#print axioms RH26E05C2.conductor_sharp_fixture
#print axioms RH26E05C2.missing_conductor_factor_control
