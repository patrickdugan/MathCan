import Mathlib

/-! Scalar witness propagation at the B22 terminal divisibility assembly.
All surrounding witnesses are fixed. No arithmetic family is realized. -/
namespace RH26E06C

noncomputable section

def ce (C Ce cD c0 : ℝ) : ℝ := max c0 (2*C+Ce+cD+3)
def finalDiv (C Ce cD c0 C3 C2 : ℝ) : ℝ :=
  max (max (60*ce C Ce cD c0) C3) (max C2 0)
def finalFloor (c0 C3 C2 : ℝ) : ℝ :=
  max (max (60*c0) C3) (max C2 0)

theorem final_floor_identity (C Ce cD c0 C3 C2 : ℝ) :
    finalDiv C Ce cD c0 C3 C2 =
      max (finalFloor c0 C3 C2) (60*(2*C+Ce+cD+3)) := by
  let v := 2*C+Ce+cD+3
  have hscale : 60*max c0 v = max (60*c0) (60*v) := by
    by_cases h : c0 ≤ v
    · rw [max_eq_right h, max_eq_right (show 60*c0 ≤ 60*v by linarith)]
    · have hh : v ≤ c0 := le_of_not_ge h
      rw [max_eq_left hh, max_eq_left (show 60*v ≤ 60*c0 by linarith)]
  change max (max (60*max c0 v) C3) (max C2 0) =
    max (max (max (60*c0) C3) (max C2 0)) (60*v)
  rw [hscale]
  apply le_antisymm
  · apply max_le
    · apply max_le
      · apply max_le
        · exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
        · exact le_max_right _ _
      · exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (le_max_right _ _).trans (le_max_left _ _)
  · apply max_le
    · apply max_le
      · apply max_le
        · exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
        · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact le_max_right _ _
    · exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem final_gain_bounds (C lo hi cD c0 C3 C2 : ℝ) (h : lo ≤ hi) :
    0 ≤ finalDiv C hi cD c0 C3 C2-finalDiv C lo cD c0 C3 C2 ∧
    finalDiv C hi cD c0 C3 C2-finalDiv C lo cD c0 C3 C2 ≤ 60*(hi-lo) := by
  rw [final_floor_identity, final_floor_identity]
  let F := finalFloor c0 C3 C2
  let l := 60*(2*C+lo+cD+3)
  let u := 60*(2*C+hi+cD+3)
  change 0 ≤ max F u-max F l ∧ max F u-max F l ≤ 60*(hi-lo)
  have hlu : l ≤ u := by dsimp [l,u]; linarith
  have hm : max F l ≤ max F u := max_le_max le_rfl hlu
  have hf : F ≤ max F l := le_max_left _ _
  have hl : l ≤ max F l := le_max_right _ _
  have hh : max F u ≤ max F l + (u-l) :=
    max_le (by linarith only [hf,hlu]) (by linarith only [hl])
  have hd : u-l = 60*(hi-lo) := by dsimp [l,u]; ring
  exact ⟨by linarith only [hm], by linarith only [hh,hd]⟩

theorem final_gain_identity (C lo hi cD c0 C3 C2 : ℝ) :
    finalDiv C hi cD c0 C3 C2-finalDiv C lo cD c0 C3 C2 =
    max (60*(2*C+hi+cD+3)-finalFloor c0 C3 C2) 0 -
      max (60*(2*C+lo+cD+3)-finalFloor c0 C3 C2) 0 := by
  have h (F v : ℝ) : max F v = F+max (v-F) 0 := by
    by_cases hv : F ≤ v
    · rw [max_eq_right hv, max_eq_left (show 0 ≤ v-F by linarith)]
      ring
    · have hv' : v ≤ F := le_of_not_ge hv
      rw [max_eq_left hv', max_eq_right (show v-F ≤ 0 by linarith)]
      ring
  rw [final_floor_identity, final_floor_identity, h (finalFloor c0 C3 C2) (60*(2*C+hi+cD+3)),
    h (finalFloor c0 C3 C2) (60*(2*C+lo+cD+3))]
  ring

theorem final_gain_control :
    finalDiv 0 100 2 28 5000 0-finalDiv 0 40 2 28 5000 0 = 1300 ∧
    finalDiv 0 100 2 28 7000 0=finalDiv 0 40 2 28 7000 0 := by
  norm_num [finalDiv,ce,max_def]

theorem split_slack (p q A B g : ℝ) (hpq : p ≤ q) (hA : 0 ≤ A) :
    q*(A+g*B)-(p*A+q*g*B) = (q-p)*A ∧
    0 ≤ q*(A+g*B)-(p*A+q*g*B) := by
  have h : q*(A+g*B)-(p*A+q*g*B) = (q-p)*A := by ring
  refine ⟨h,?_⟩
  rw [h]
  exact mul_nonneg (sub_nonneg.mpr hpq) hA

theorem inflated_slack (p q A B g : ℝ) (hpq : p ≤ q)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hg : 1 ≤ g) :
    q*(A+g^2*B)-(p*A+q*g*B) = (q-p)*A+q*(g^2-g)*B ∧
    0 ≤ q*(A+g^2*B)-(p*A+q*g*B) := by
  have h : q*(A+g^2*B)-(p*A+q*g*B) = (q-p)*A+q*(g^2-g)*B := by ring
  refine ⟨h,?_⟩
  rw [h]
  have h0 : 0 ≤ g := by linarith
  have h1 : 0 ≤ g-1 := by linarith
  have h2 : 0 ≤ g^2-g := by nlinarith only [mul_nonneg h0 h1]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hpq) hA) (mul_nonneg (mul_nonneg hq h2) hB)

theorem effective_coefficient (p q A B g : ℝ) (hpq : p ≤ q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hg : 1 ≤ g) (hd : 0 < A+g*B) :
    p ≤ (p*A+q*g*B)/(A+g*B) ∧ (p*A+q*g*B)/(A+g*B) ≤ q := by
  have hgb : 0 ≤ g*B := mul_nonneg (by linarith) hB
  have h1 := mul_le_mul_of_nonneg_right hpq hgb
  have h2 := mul_le_mul_of_nonneg_right hpq hA
  constructor
  · apply (le_div_iff₀ hd).2
    nlinarith only [h1]
  · apply (div_le_iff₀ hd).2
    nlinarith only [h2]

theorem common_sharp (p q g K : ℝ) (hpq : p ≤ q) (hg : 1 ≤ g) :
    (∀ A B : ℝ, 0 ≤ A → 0 ≤ B → p*A+q*g*B ≤ K*(A+g*B)) ↔ q ≤ K := by
  constructor
  · intro h
    have hh := h 0 1 (by norm_num) (by norm_num)
    simp at hh
    by_contra! hn
    have hp : 0 < (q-K)*g := mul_pos (by linarith) (by linarith)
    nlinarith only [hh,hp]
  · intro h A B hA hB
    have hgb : 0 ≤ g*B := mul_nonneg (by linarith) hB
    have h1 := mul_le_mul_of_nonneg_right (hpq.trans h) hA
    have h2 := mul_le_mul_of_nonneg_right h hgb
    nlinarith only [h1,h2]

theorem five_term_absorption (x b E d a1 a2 a3 a4 a5 : ℝ)
    (hx : 1 ≤ x) (hb : 0 ≤ b) (hd : 0 < d) (h5 : 5 ≤ x^d)
    (h1 : a1 ≤ x^E*b) (h2 : a2 ≤ x^E*b) (h3 : a3 ≤ x^E*b)
    (h4 : a4 ≤ x^E*b) (h5a : a5 ≤ x^E*b) :
    a1+a2+a3+a4+a5 ≤ x^(E+d)*b := by
  have hx0 : 0 < x := by linarith
  have hpos : 0 ≤ x^E*b := mul_nonneg (Real.rpow_nonneg hx0.le _) hb
  calc
    _ ≤ 5*(x^E*b) := by linarith only [h1,h2,h3,h4,h5a]
    _ ≤ x^d*(x^E*b) := mul_le_mul_of_nonneg_right h5 hpos
    _ = _ := by rw [Real.rpow_add hx0]; ring

theorem eventual_five_term (d : ℝ) (hd : 0 < d) :
    ∃ x0 : ℝ, x0=max 1 (5^(1/d)) ∧ 1 ≤ x0 ∧ ∀ x ≥ x0, 5 ≤ x^d := by
  refine ⟨max 1 (5^(1/d)),rfl,le_max_left _ _,?_⟩
  intro x hx
  have hxd : (5:ℝ)^(1/d) ≤ x := (le_max_right _ _).trans hx
  have hpow : ((5:ℝ)^(1/d))^d = 5 := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 5)]
    rw [show 1/d*d = 1 by field_simp [hd.ne']]
    exact Real.rpow_one _
  calc
    (5:ℝ) = ((5:ℝ)^(1/d))^d := hpow.symm
    _ ≤ x^d := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hxd hd.le

end
end RH26E06C

#print axioms RH26E06C.final_floor_identity
#print axioms RH26E06C.final_gain_bounds
#print axioms RH26E06C.final_gain_identity
#print axioms RH26E06C.final_gain_control
#print axioms RH26E06C.split_slack
#print axioms RH26E06C.inflated_slack
#print axioms RH26E06C.effective_coefficient
#print axioms RH26E06C.common_sharp
#print axioms RH26E06C.five_term_absorption
#print axioms RH26E06C.eventual_five_term
