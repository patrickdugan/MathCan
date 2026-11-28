import Mathlib

/-! Scalar certificates for signed ideal rounding and the source DGam cap.
These are independent conditional statements; no arithmetic host is asserted. -/
namespace RH26E06D

noncomputable section

def gap (y : ℝ) : ℝ := y - (⌊y⌋ : ℝ)

def err {ι : Type*} (S : Finset ι) (a y : ι → ℝ) : ℝ :=
  ∑ i ∈ S, a i * ((⌊y i⌋ : ℝ) - y i)

def active {ι : Type*} (S : Finset ι) (y : ι → ℝ) : Finset ι := by
  classical
  exact S.filter (fun i => gap (y i) ≠ 0)

theorem floor_gap (y : ℝ) : 0 ≤ gap y ∧ gap y < 1 := by
  unfold gap
  exact ⟨by linarith [Int.floor_le y], by linarith [Int.lt_floor_add_one y]⟩

theorem signed_identity {ι : Type*} (S : Finset ι) (a y : ι → ℝ) :
    err S a y = -(∑ i ∈ S, a i * gap (y i)) := by
  unfold err
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold gap
  ring

theorem signed_bounds {ι : Type*} (S : Finset ι) (a y : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) :
    err S a y ≤ 0 ∧ -(∑ i ∈ S, a i) ≤ err S a y := by
  rw [signed_identity]
  have h0 : 0 ≤ ∑ i ∈ S, a i * gap (y i) :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (floor_gap (y i)).1)
  have h1 : (∑ i ∈ S, a i * gap (y i)) ≤ ∑ i ∈ S, a i := by
    apply Finset.sum_le_sum
    intro i hi
    calc
      a i * gap (y i) ≤ a i * 1 :=
        mul_le_mul_of_nonneg_left (floor_gap (y i)).2.le (ha i hi)
      _ = a i := mul_one _
  exact ⟨by linarith only [h0], by linarith only [h1]⟩

private theorem sum_active {ι : Type*} (S : Finset ι) (a y : ι → ℝ) :
    (∑ i ∈ active S y, a i * gap (y i)) =
      ∑ i ∈ S, a i * gap (y i) := by
  classical
  unfold active
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : gap (y i) = 0 <;> simp [h]

theorem active_support_bound {ι : Type*} (S : Finset ι) (a y : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) :
    |err S a y| ≤ ∑ i ∈ active S y, a i := by
  classical
  rw [abs_of_nonpos (signed_bounds S a y ha).1, signed_identity, neg_neg,
    ← sum_active S a y]
  apply Finset.sum_le_sum
  intro i hi
  have hs : i ∈ S := (Finset.mem_filter.mp (show i ∈ S.filter (fun j => gap (y j) ≠ 0) from hi)).1
  calc
    a i * gap (y i) ≤ a i * 1 :=
      mul_le_mul_of_nonneg_left (floor_gap (y i)).2.le (ha i hs)
    _ = a i := mul_one _

theorem integral_zero {ι : Type*} (S : Finset ι) (a y : ι → ℝ)
    (hy : ∀ i ∈ S, y i = (⌊y i⌋ : ℝ)) : err S a y = 0 := by
  unfold err
  apply Finset.sum_eq_zero
  intro i hi
  rw [sub_eq_zero.mpr (hy i hi).symm, mul_zero]

theorem strict_active_bound {ι : Type*} (S : Finset ι) (a y : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hpos : ∃ i ∈ active S y, 0 < a i) :
    |err S a y| < ∑ i ∈ active S y, a i := by
  classical
  rw [abs_of_nonpos (signed_bounds S a y ha).1, signed_identity, neg_neg,
    ← sum_active S a y]
  apply Finset.sum_lt_sum
  · intro i hi
    have hs : i ∈ S := (Finset.mem_filter.mp (show i ∈ S.filter (fun j => gap (y j) ≠ 0) from hi)).1
    calc
      a i * gap (y i) ≤ a i * 1 :=
        mul_le_mul_of_nonneg_left (floor_gap (y i)).2.le (ha i hs)
      _ = a i := mul_one _
  · obtain ⟨i, hi, hp⟩ := hpos
    exact ⟨i, hi, by simpa using mul_lt_mul_of_pos_left (floor_gap (y i)).2 hp⟩

theorem dg_product_8 (n N X x l : ℝ)
    (hn : 0 ≤ n) (hN : 0 ≤ N) (hX : 0 ≤ X) (hx : 0 ≤ x) (hl : 0 ≤ l)
    (hNX : N ≤ X) (hlx : l ≤ 4*x) :
    2*n*N*l ≤ 8*(X*x*n) := by
  have h1 : 2*n*N ≤ 2*n*X := mul_le_mul_of_nonneg_left hNX (by positivity)
  calc
    2*n*N*l ≤ (2*n*X)*(4*x) :=
      mul_le_mul h1 hlx hl (by positivity)
    _ = _ := by ring

theorem dgam_log_8 (L C P Xpp : ℝ) (hL : L ≤ C*P) (hP : 0 ≤ P)
    (hPX : P ≤ 8*Xpp) : L ≤ 8*(abs C)*Xpp := by
  calc
    L ≤ C*P := hL
    _ ≤ (abs C)*P := mul_le_mul_of_nonneg_right (le_abs_self C) hP
    _ ≤ (abs C)*(8*Xpp) := mul_le_mul_of_nonneg_left hPX (abs_nonneg C)
    _ = _ := by ring

def muOld (C : ℝ) : ℝ := 2*(Real.log 4+5+10*abs C)
def muNew (C : ℝ) : ℝ := 2*(Real.log 4+5+8*abs C)

theorem mu_gain (C : ℝ) : muOld C-muNew C = 4*abs C ∧ 0 ≤ muOld C-muNew C := by
  have h : muOld C-muNew C = 4*abs C := by unfold muOld muNew; ring
  refine ⟨h,?_⟩
  rw [h]
  positivity

theorem rounding_controls :
    err ({()} : Finset Unit) (fun _ => 2) (fun _ => (-1/4 : ℝ)) = -3/2 ∧
    err ({()} : Finset Unit) (fun _ => 2) (fun _ => (-1 : ℝ)) = 0 ∧
    err ({()} : Finset Unit) (fun _ => 2) (fun _ => (3/4 : ℝ)) = -3/2 := by
  have h1 : ⌊(-1/4 : ℝ)⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr (by norm_num)
  have h2 : ⌊(-1 : ℝ)⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr (by norm_num)
  have h3 : ⌊(3/4 : ℝ)⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr (by norm_num)
  simp only [err, Finset.sum_singleton, h1, h2, h3]
  norm_num

end
end RH26E06D

#print axioms RH26E06D.floor_gap
#print axioms RH26E06D.signed_identity
#print axioms RH26E06D.signed_bounds
#print axioms RH26E06D.active_support_bound
#print axioms RH26E06D.integral_zero
#print axioms RH26E06D.strict_active_bound
#print axioms RH26E06D.dg_product_8
#print axioms RH26E06D.dgam_log_8
#print axioms RH26E06D.mu_gain
#print axioms RH26E06D.rounding_controls
