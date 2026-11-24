import Mathlib

/-! Scalar consequences of B16. The arithmetic rank and cohomology
realization remains external. q denotes sqrt(b), F denotes f*m. -/
namespace RH26E06A

noncomputable section

def base (F q g : ℝ) : ℝ := F*q^2*g
def weight (F q g N : ℝ) : ℝ := g*(base F q g+N)

theorem exact_slack (F q g N z R K V η : ℝ)
    (hF : 1 ≤ F) (hq : 1 ≤ q) (hg : 1 ≤ g)
    (hN : 0 ≤ N) (hz : 0 ≤ z) (hzg : z ≤ g)
    (hR : 0 ≤ R) (hV : V ≤ q)
    (hη : η ≤ R*(K*(g*base F q g+z*N)+V)) :
    η ≤ R*((abs K)*weight F q g N+q-(abs K)*(g-z)*N) := by
  have hF0 : 0 ≤ F := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hbase : 0 ≤ base F q g := by unfold base; positivity
  have hnum : 0 ≤ g*base F q g+z*N := by positivity
  have hk := mul_le_mul_of_nonneg_right (le_abs_self K) hnum
  apply hη.trans
  apply mul_le_mul_of_nonneg_left _ hR
  calc
    _ ≤ (abs K)*(g*base F q g+z*N)+q := add_le_add hk hV
    _ = _ := by unfold weight; ring

theorem cohomology_budget (F q g N : ℝ)
    (hF : 1 ≤ F) (hq : 1 ≤ q) (hg : 1 ≤ g) (hN : 0 ≤ N) :
    q ≤ (1/(F*g^2*q))*weight F q g N := by
  have hF0 : 0 < F := by linarith
  have hq0 : 0 < q := by linarith
  have hg0 : 0 < g := by linarith
  have hd : 0 < F*g^2*q := by positivity
  have hw : q*(F*g^2*q) ≤ weight F q g N := by
    unfold weight base
    have hn : 0 ≤ g*N := mul_nonneg hg0.le hN
    nlinarith only [hn]
  calc
    q = (1/(F*g^2*q))*(q*(F*g^2*q)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

theorem refined_conversion (F q g N z R K V η : ℝ)
    (hF : 1 ≤ F) (hq : 1 ≤ q) (hg : 1 ≤ g)
    (hN : 0 ≤ N) (hz : 0 ≤ z) (hzg : z ≤ g)
    (hR : 0 ≤ R) (hV : V ≤ q)
    (hη : η ≤ R*(K*(g*base F q g+z*N)+V)) :
    η ≤ R*(((abs K)+1/(F*g^2*q))*weight F q g N) := by
  have hs := exact_slack F q g N z R K V η hF hq hg hN hz hzg hR hV hη
  have hb := cohomology_budget F q g N hF hq hg hN
  have hsl : 0 ≤ (abs K)*(g-z)*N := by
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hzg)) hN
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ hR
  calc
    _ ≤ (abs K)*weight F q g N+q := by linarith only [hsl]
    _ ≤ (abs K)*weight F q g N+(1/(F*g^2*q))*weight F q g N := by linarith only [hb]
    _ = _ := by ring

theorem delta_budget (F q g N δ : ℝ)
    (hF : 1 ≤ F) (hq : 1 ≤ q) (hg : 1 ≤ g) (hN : 0 ≤ N)
    (hδ : 0 ≤ δ) (hδg : 1 ≤ δ*g^2) :
    q ≤ δ*weight F q g N := by
  have hq0 : 0 ≤ q := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hq2 : q ≤ q^2 := by nlinarith only [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hFq : q^2 ≤ F*q^2 := le_mul_of_one_le_left (sq_nonneg q) hF
  have hw : q*g^2 ≤ weight F q g N := by
    have hh := mul_le_mul_of_nonneg_right (hq2.trans hFq) (sq_nonneg g)
    have hn := mul_nonneg hg0 hN
    unfold weight base
    nlinarith only [hh, hn]
  calc
    q = 1*q := by ring
    _ ≤ (δ*g^2)*q := mul_le_mul_of_nonneg_right hδg hq0
    _ = δ*(q*g^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw hδ

theorem delta_conversion (F q g N z R K V η δ : ℝ)
    (hF : 1 ≤ F) (hq : 1 ≤ q) (hg : 1 ≤ g)
    (hN : 0 ≤ N) (hz : 0 ≤ z) (hzg : z ≤ g)
    (hR : 0 ≤ R) (hV : V ≤ q)
    (hη : η ≤ R*(K*(g*base F q g+z*N)+V))
    (hδ : 0 ≤ δ) (hδg : 1 ≤ δ*g^2) :
    η ≤ R*(((abs K)+δ)*weight F q g N) := by
  have hs := exact_slack F q g N z R K V η hF hq hg hN hz hzg hR hV hη
  have hb := delta_budget F q g N δ hF hq hg hN hδ hδg
  have hsl : 0 ≤ (abs K)*(g-z)*N := mul_nonneg (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hzg)) hN
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ hR
  calc
    _ ≤ (abs K)*weight F q g N+q := by linarith only [hsl]
    _ ≤ (abs K)*weight F q g N+δ*weight F q g N := by linarith only [hb]
    _ = _ := by ring

theorem eventual_delta (eps δ : ℝ) (he : 0 < eps) (hd : 0 < δ) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x → 1 ≤ δ*(x^eps)^2 := by
  let M : ℝ := max 1 (1/δ)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := by linarith
  have hmd : 1/δ ≤ M := le_max_right _ _
  refine ⟨max 1 (M^(1/eps)), le_max_left _ _, ?_⟩
  intro x hx
  have hxM : M^(1/eps) ≤ x := (le_max_right _ _).trans hx
  have hm : (1/eps)*eps = 1 := by field_simp
  have hMg : M ≤ x^eps := by
    calc
      M = (M^(1/eps))^eps := by rw [← Real.rpow_mul hM0, hm, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hxM he.le
  have hg : 1 ≤ x^eps := hM.trans hMg
  have hg0 : 0 ≤ x^eps := by linarith
  have hh : 1 ≤ δ*(x^eps) := by
    have hp := mul_le_mul_of_nonneg_left (hmd.trans hMg) hd.le
    have hone : δ*(1/δ) = 1 := by field_simp
    linarith only [hp, hone]
  have hs : x^eps ≤ (x^eps)^2 := by nlinarith only [mul_nonneg hg0 (sub_nonneg.mpr hg)]
  exact hh.trans (mul_le_mul_of_nonneg_left hs hd.le)

theorem zero_extra_if_slack (F q g N z R K V η : ℝ)
    (hF : 1 ≤ F) (hq : 1 ≤ q) (hg : 1 ≤ g)
    (hN : 0 ≤ N) (hz : 0 ≤ z) (hzg : z ≤ g)
    (hR : 0 ≤ R) (hV : V ≤ q)
    (hη : η ≤ R*(K*(g*base F q g+z*N)+V))
    (hsl : q ≤ (abs K)*(g-z)*N) :
    η ≤ R*((abs K)*weight F q g N) := by
  apply (exact_slack F q g N z R K V η hF hq hg hN hz hzg hR hV hη).trans
  exact mul_le_mul_of_nonneg_left (by linarith only [hsl]) hR

theorem zero_extra_control :
    ∃ F q g N z R K V η : ℝ,
      1 ≤ F ∧ 1 ≤ q ∧ 1 ≤ g ∧ 0 ≤ N ∧ 0 ≤ z ∧ z ≤ g ∧
      0 ≤ R ∧ V ≤ q ∧ η ≤ R*(K*(g*base F q g+z*N)+V) ∧
      R*((abs K)*weight F q g N) < η := by
  refine ⟨1, 1, 1, 0, 0, 1, 1, 1, 2, ?_⟩
  norm_num [base, weight]

end
end RH26E06A

#print axioms RH26E06A.exact_slack
#print axioms RH26E06A.cohomology_budget
#print axioms RH26E06A.refined_conversion
#print axioms RH26E06A.delta_budget
#print axioms RH26E06A.delta_conversion
#print axioms RH26E06A.eventual_delta
#print axioms RH26E06A.zero_extra_if_slack
#print axioms RH26E06A.zero_extra_control
