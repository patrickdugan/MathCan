import Mathlib

/-! Independent scalar refinement of the B26 error-window witness. -/
namespace RH26E06E
noncomputable section

def ksum (d c s v l : ℝ) : ℝ := d+c+s+v+l+6
def kmax (d c s v l : ℝ) : ℝ := max 6 (max d (max c (max s (max v l))))
def big (K H e : ℝ) : ℝ := 200*(1+K)^2*(1+H)*(1+e)

theorem max_dominates (d c s v l : ℝ) :
    6 ≤ kmax d c s v l ∧ d ≤ kmax d c s v l ∧
    c ≤ kmax d c s v l ∧ s ≤ kmax d c s v l ∧
    v ≤ kmax d c s v l ∧ l ≤ kmax d c s v l := by
  unfold kmax
  simp only [le_max_iff, le_refl, true_or, or_true, and_self]

theorem max_minimal (d c s v l K : ℝ) (h6 : 6 ≤ K)
    (hd : d ≤ K) (hc : c ≤ K) (hs : s ≤ K) (hv : v ≤ K) (hl : l ≤ K) :
    kmax d c s v l ≤ K := by
  unfold kmax
  exact max_le h6 (max_le hd (max_le hc (max_le hs (max_le hv hl))))

theorem sum_max_bounds (d c s v l : ℝ)
    (hd : 0 ≤ d) (hc : 0 ≤ c) (hs : 0 ≤ s) (hv : 0 ≤ v) (hl : 0 ≤ l) :
    kmax d c s v l ≤ ksum d c s v l ∧
    ksum d c s v l ≤ 6*kmax d c s v l := by
  obtain ⟨a,b,c',s',v',l'⟩ := max_dominates d c s v l
  constructor
  · apply max_minimal <;> unfold ksum <;> linarith
  · unfold ksum
    linarith only [a,b,c',s',v',l']

theorem frame_budget (d c s v l F b A g : ℝ)
    (hF : F ≤ 6*b) (hb : 0 ≤ b) (hbA : b ≤ A) (hg : 1 ≤ g) :
    F ≤ kmax d c s v l*g*A := by
  have hk := (max_dominates d c s v l).1
  have hk0 : 0 ≤ kmax d c s v l := by linarith
  have hA : 0 ≤ A := hb.trans hbA
  calc
    F ≤ 6*b := hF
    _ ≤ kmax d c s v l*b := mul_le_mul_of_nonneg_right hk hb
    _ ≤ kmax d c s v l*A := mul_le_mul_of_nonneg_left hbA hk0
    _ ≤ (kmax d c s v l*g)*A :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hk0 hg) hA

theorem kbig_mono (lo hi H e : ℝ) (hlo : 0 ≤ lo) (h : lo ≤ hi)
    (hH : 0 ≤ H) (he : 0 ≤ e) : big lo H e ≤ big hi H e := by
  have hs : (1+lo)^2 ≤ (1+hi)^2 := by
    have hh : 0 ≤ (hi-lo)*(2+hi+lo) := mul_nonneg (by linarith) (by linarith)
    nlinarith only [hh]
  unfold big
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by norm_num)) (by linarith)) (by linarith)

theorem kbig_ratio (d c s v l H e : ℝ)
    (hd : 0 ≤ d) (hc : 0 ≤ c) (hs : 0 ≤ s) (hv : 0 ≤ v) (hl : 0 ≤ l)
    (hH : 0 ≤ H) (he : 0 ≤ e) :
    big (kmax d c s v l) H e ≤ big (ksum d c s v l) H e ∧
    big (ksum d c s v l) H e < 36*big (kmax d c s v l) H e := by
  obtain ⟨h1,h2⟩ := sum_max_bounds d c s v l hd hc hs hv hl
  have hk := (max_dominates d c s v l).1
  have hm0 : 0 ≤ kmax d c s v l := by linarith
  refine ⟨kbig_mono _ _ H e hm0 h1 hH he,?_⟩
  have ha : 1+ksum d c s v l < 6*(1+kmax d c s v l) := by linarith only [h2]
  have hb : 0 < 6*(1+kmax d c s v l)+(1+ksum d c s v l) := by linarith
  have hsq : (1+ksum d c s v l)^2 < 36*(1+kmax d c s v l)^2 := by
    nlinarith only [mul_pos (sub_pos.mpr ha) hb]
  have h' := mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_left hsq (by norm_num : (0:ℝ) < 200))
      (show 0 < 1+H by linarith))
    (show 0 < 1+e by linarith)
  unfold big
  nlinarith only [h']

theorem threshold_equivalence (eps B x : ℝ) (he : 0 < eps) (hB : 0 < B)
    (hx : 1 ≤ x) : B ≤ x^eps ↔ B^(1/eps) ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have hinv : 0 ≤ 1/eps := by positivity
  have hmul1 : eps*(1/eps)=1 := by field_simp [he.ne']
  have hmul2 : (1/eps)*eps=1 := by field_simp [he.ne']
  constructor
  · intro h
    have hh := Real.rpow_le_rpow hB.le h hinv
    rw [← Real.rpow_mul hx0, hmul1, Real.rpow_one] at hh
    exact hh
  · intro h
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hB.le _) h he.le
    rw [← Real.rpow_mul hB.le, hmul2, Real.rpow_one] at hh
    exact hh

theorem threshold_gain (d c s v l H e eps : ℝ)
    (hd : 0 ≤ d) (hc : 0 ≤ c) (hs : 0 ≤ s) (hv : 0 ≤ v) (hl : 0 ≤ l)
    (hH : 0 ≤ H) (he : 0 ≤ e) (hep : 0 < eps) :
    (big (kmax d c s v l) H e)^(1/eps) ≤ (big (ksum d c s v l) H e)^(1/eps) ∧
    (big (ksum d c s v l) H e)^(1/eps) <
      (36:ℝ)^(1/eps)*(big (kmax d c s v l) H e)^(1/eps) := by
  obtain ⟨h1,h2⟩ := kbig_ratio d c s v l H e hd hc hs hv hl hH he
  have hK := (max_dominates d c s v l).1
  have hp : 0 < big (kmax d c s v l) H e := by
    unfold big
    have hbase : 0 < 1+kmax d c s v l := by linarith
    positivity
  have hp' : 0 < big (ksum d c s v l) H e := hp.trans_le h1
  have hr : 0 < 1/eps := by positivity
  refine ⟨Real.rpow_le_rpow hp.le h1 hr.le,?_⟩
  have hh := Real.rpow_lt_rpow hp'.le h2 hr
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 36) hp.le] at hh
  exact hh

def familyMax (base : ℝ) (xs : List ℝ) : ℝ := xs.foldr max base

theorem family_threshold (base : ℝ) (xs : List ℝ) (hb : 1 ≤ base) :
    base ≤ familyMax base xs ∧
    (∀ t ∈ xs, t ≤ familyMax base xs) ∧
    familyMax base xs ≤ base+(xs.map abs).sum := by
  induction xs with
  | nil => simp [familyMax]
  | cons a xs ih =>
    obtain ⟨hbase, hall, hupper⟩ := ih
    have hnonneg : 0 ≤ (xs.map abs).sum := by
      induction xs with
      | nil => simp
      | cons t ts ih' => simp only [List.map_cons,List.sum_cons]; linarith [abs_nonneg t]
    change base ≤ max a (familyMax base xs) ∧
      (∀ t ∈ a::xs, t ≤ max a (familyMax base xs)) ∧
      max a (familyMax base xs) ≤ base+(abs a+(xs.map abs).sum)
    refine ⟨hbase.trans (le_max_right _ _),?_,?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact le_max_left _ _
      · exact (hall t ht).trans (le_max_right _ _)
    · exact max_le (by linarith [le_abs_self a]) (by linarith [abs_nonneg a])

theorem floor_controls :
    kmax 6 6 6 6 6 = 6 ∧ ksum 6 6 6 6 6 = 36 ∧
    big (ksum 6 6 6 6 6) 0 0 / big (kmax 6 6 6 6 6) 0 0 = (37/7:ℝ)^2 ∧
    kmax 90 100 0 0 0 = 100 ∧ kmax 1 100 0 0 0 = 100 := by
  norm_num [kmax,ksum,big,max_def]

end
end RH26E06E

#print axioms RH26E06E.max_dominates
#print axioms RH26E06E.max_minimal
#print axioms RH26E06E.sum_max_bounds
#print axioms RH26E06E.frame_budget
#print axioms RH26E06E.kbig_mono
#print axioms RH26E06E.kbig_ratio
#print axioms RH26E06E.threshold_equivalence
#print axioms RH26E06E.threshold_gain
#print axioms RH26E06E.family_threshold
#print axioms RH26E06E.floor_controls
