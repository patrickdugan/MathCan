import RankOneCharacter

/-! VPVNP-02J: normalized Walsh energy and sharp binary matrix observer bound. -/
open scoped BigOperators
open Finset
namespace VPVNP.Binary
noncomputable section

attribute [local instance] unitMatrixFintype rankOneFintype

section Energy
variable {I T J : Type*} [Fintype I] [DecidableEq I] [Fintype T]

def oddProb (inc : T → Bits I) (b : Bits I) : ℝ :=
  (1-(∑ t : T, walsh b (inc t))/(Fintype.card T : ℝ))/2

def scalarEnergy (inc : T → Bits I) (f : Bits I → ℝ) : ℝ :=
  (∑ t : T, ∑ a : Bits I, (f (a+inc t)-f a)^2) /
    ((Fintype.card (Bits I) : ℝ)*(Fintype.card T : ℝ))

def vectorEnergy [Fintype J] (inc : T → Bits I) (f : Bits I → J → ℝ) : ℝ :=
  ∑ j : J, scalarEnergy inc (fun a => f a j)

def observerWeight [Fintype J] (f : Bits I → J → ℝ) (b : Bits I) : ℝ :=
  ∑ j : J, (walshCoeff (fun a => f a j) b)^2

theorem oddProb_zero (inc : T → Bits I) (hT : 0 < Fintype.card T) :
    oddProb inc 0 = 0 := by
  have hM : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold oddProb
  simp [walsh,bitSign,pairing_zero_left,hM]

theorem oddProb_nonneg (inc : T → Bits I) (hT : 0 < Fintype.card T) (b : Bits I) :
    0 ≤ oddProb inc b := by
  have hM : 0 < (Fintype.card T : ℝ) := by exact_mod_cast hT
  have hs : (∑ t : T, walsh b (inc t)) ≤ ∑ _ : T, (1:ℝ) := by
    apply Finset.sum_le_sum
    intro t ht
    rcases walsh_sign b (inc t) with h | h <;> rw [h] <;> norm_num
  have hdiv : (∑ t : T, walsh b (inc t))/(Fintype.card T : ℝ) ≤ 1 :=
    (div_le_iff₀ hM).2 (by simpa using hs)
  unfold oddProb
  linarith

theorem charShift_sum (inc : T → Bits I) (b : Bits I) :
    (∑ t : T, (walsh b (inc t)-1)^2) =
      2*((Fintype.card T : ℝ)-∑ t : T, walsh b (inc t)) := by
  calc
    _ = ∑ t : T, 2*(1-walsh b (inc t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rcases walsh_sign b (inc t) with h | h <;> rw [h] <;> norm_num
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp

theorem scalar_energy_spectral (inc : T → Bits I) (hT : 0 < Fintype.card T)
    (f : Bits I → ℝ) :
    scalarEnergy inc f = 4*∑ b : Bits I, (walshCoeff f b)^2 * oddProb inc b := by
  have hN : (Fintype.card (Bits I) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Bits I) ≠ 0)
  have hM : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hs : (∑ t : T, ∑ a : Bits I, (f (a+inc t)-f a)^2) =
      (Fintype.card (Bits I) : ℝ) *
        ∑ b : Bits I, (walshCoeff f b)^2 * ∑ t : T, (walsh b (inc t)-1)^2 := by
    calc
      _ = ∑ t : T, (Fintype.card (Bits I) : ℝ) *
          ∑ b : Bits I, (walshCoeff f b * (walsh b (inc t)-1))^2 := by
        apply Finset.sum_congr rfl
        intro t ht
        exact actual_shift_energy f (inc t)
      _ = (Fintype.card (Bits I) : ℝ) *
          ∑ t : T, ∑ b : Bits I, (walshCoeff f b * (walsh b (inc t)-1))^2 := by
        rw [Finset.mul_sum]
      _ = (Fintype.card (Bits I) : ℝ) *
          ∑ b : Bits I, ∑ t : T, (walshCoeff f b * (walsh b (inc t)-1))^2 := by
        congr 1
        exact Finset.sum_comm
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        ring
  unfold scalarEnergy
  rw [hs]
  calc
    _ = (∑ b : Bits I, (walshCoeff f b)^2 * ∑ t : T, (walsh b (inc t)-1)^2) /
        (Fintype.card T : ℝ) := by field_simp [hN,hM]
    _ = ∑ b : Bits I, ((walshCoeff f b)^2 * ∑ t : T, (walsh b (inc t)-1)^2) /
        (Fintype.card T : ℝ) := by rw [Finset.sum_div]
    _ = ∑ b : Bits I, 4*((walshCoeff f b)^2 * oddProb inc b) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [charShift_sum]
      unfold oddProb
      field_simp [hM] <;> ring
    _ = _ := by rw [Finset.mul_sum]

theorem vector_energy_mean [Fintype J] (inc : T → Bits I) (f : Bits I → J → ℝ) :
    vectorEnergy inc f =
      (∑ t : T, ∑ a : Bits I, ∑ j : J, (f (a+inc t) j-f a j)^2) /
        ((Fintype.card (Bits I) : ℝ)*(Fintype.card T : ℝ)) := by
  unfold vectorEnergy scalarEnergy
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.sum_comm

theorem vector_energy_spectral [Fintype J] (inc : T → Bits I)
    (hT : 0 < Fintype.card T) (f : Bits I → J → ℝ) :
    vectorEnergy inc f = 4*∑ b : Bits I, observerWeight f b * oddProb inc b := by
  unfold vectorEnergy
  simp_rw [scalar_energy_spectral inc hT]
  calc
    _ = 4*∑ j : J, ∑ b : Bits I, (walshCoeff (fun a => f a j) b)^2 * oddProb inc b := by
      rw [Finset.mul_sum]
    _ = 4*∑ b : Bits I, ∑ j : J, (walshCoeff (fun a => f a j) b)^2 * oddProb inc b := by
      congr 1
      exact Finset.sum_comm
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      unfold observerWeight
      rw [Finset.sum_mul]

theorem observer_weight_nonneg [Fintype J] (f : Bits I → J → ℝ) (b : Bits I) :
    0 ≤ observerWeight f b := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- A nonconstant finite vector map has positive energy in a nonzero Walsh mode. -/
theorem nonconstant_has_mode [Fintype J] (f : Bits I → J → ℝ)
    (hf : ∃ a a', f a ≠ f a') :
    ∃ b : Bits I, b ≠ 0 ∧ 0 < observerWeight f b := by
  classical
  by_contra h
  have hz (b : Bits I) (hb : b ≠ 0) : observerWeight f b = 0 :=
    le_antisymm (le_of_not_gt (fun hp => h ⟨b,hb,hp⟩)) (observer_weight_nonneg f b)
  obtain ⟨a,a',ha⟩ := hf
  apply ha
  funext j
  rw [walsh_reconstruct (fun x => f x j) a, walsh_reconstruct (fun x => f x j) a']
  apply Finset.sum_congr rfl
  intro b hb
  by_cases he : b=0
  · subst b
    simp [walsh,bitSign,pairing_zero_left]
  · have hle : (walshCoeff (fun x => f x j) b)^2 ≤ observerWeight f b :=
      Finset.single_le_sum (fun i _ => sq_nonneg (walshCoeff (fun x => f x i) b)) (mem_univ j)
    rw [hz b he] at hle
    have hc : walshCoeff (fun x => f x j) b = 0 := by
      by_contra hne
      have hp := sq_pos_of_ne_zero hne
      linarith
    simp [hc]

def characterObserver (b : Bits I) : Bits I → Unit → ℝ := fun a _ => walsh b a

theorem character_coeff (b c : Bits I) :
    walshCoeff (walsh b) c = if b=c then 1 else 0 := by
  classical
  have hN : (Fintype.card (Bits I) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Bits I) ≠ 0)
  unfold walshCoeff
  rw [walsh_orthogonal]
  by_cases h : b=c <;> simp [h,hN]

theorem character_weight (b c : Bits I) :
    observerWeight (characterObserver b) c = if b=c then 1 else 0 := by
  classical
  unfold observerWeight characterObserver
  simp only [character_coeff]
  by_cases h : b=c <;> simp [h]

theorem character_energy (inc : T → Bits I) (hT : 0 < Fintype.card T) (b : Bits I) :
    vectorEnergy inc (characterObserver b) = 4*oddProb inc b := by
  classical
  rw [vector_energy_spectral inc hT]
  congr 1
  simp_rw [character_weight]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c hc hne
    simp [Ne.symm hne]
  · simp

end Energy

section RankBounds

theorem two_pow_ge_one (n : ℕ) : (1:ℝ) ≤ (2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; linarith

theorem full_den_ge_one (n : ℕ) : 1 ≤ (2:ℝ)^(n+1)-1 := by
  rw [pow_succ]
  linarith [two_pow_ge_one n]

theorem rankValue_abs_le_one (n k : ℕ) (hk : k ≤ n) :
    |rankValue n k| ≤ 1 := by
  induction n generalizing k with
  | zero =>
    have he : k=0 := by omega
    subst k
    rw [rankValue_zero]
    norm_num
  | succ n ih =>
    cases k with
    | zero => rw [rankValue_zero]; norm_num
    | succ k =>
      have hd := full_den_ge_one n
      have hp : 0 < (2:ℝ)^(n+1)-1 := by linarith
      rw [rankValue_step,abs_div,abs_neg,abs_of_pos hp]
      apply (div_le_iff₀ hp).2
      rw [one_mul]
      exact (ih k (by omega)).trans hd

theorem rankValue_lower (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    -(1/((2:ℝ)^n-1)) ≤ rankValue n k := by
  cases n with
  | zero => omega
  | succ n =>
    cases k with
    | zero => omega
    | succ k =>
      have hh : rankValue n k ≤ 1 := (le_abs_self _).trans (rankValue_abs_le_one n k (by omega))
      have hp : 0 ≤ (2:ℝ)^(n+1)-1 := (zero_le_one.trans (full_den_ge_one n))
      rw [rankValue_step, ← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hp

theorem rankValue_one (n : ℕ) (hn : 0 < n) :
    rankValue n 1 = -(1/((2:ℝ)^n-1)) := by
  cases n with
  | zero => omega
  | succ n => rw [rankValue_step,rankValue_zero,neg_div]

theorem two_pow_half (n : ℕ) (hn : 0 < n) :
    (2:ℝ)^(n-1) = (2:ℝ)^n/2 := by
  cases n with
  | zero => omega
  | succ n => simp only [Nat.succ_sub_one,pow_succ]; ring

theorem rank_kernel_half (n k : ℕ) (hk : 0 < k) :
    (2:ℝ)^(n-k) ≤ (2:ℝ)^n/2 := by
  by_cases hn : 0 < n
  · rw [← two_pow_half n hn]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · have hn0 : n=0 := by omega
    subst n
    norm_num at hk ⊢

theorem rank_kernel_quarter (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (2:ℝ)^(n-k) ≤ (2:ℝ)^n/4 := by
  have hn : 2 ≤ n := hk.trans hkn
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      calc
        _ ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = _ := by rw [pow_succ,pow_succ]; ring

end RankBounds

abbrev MatrixBits (n : ℕ) := Bits (Fin n × Fin n)

def matrixOf {n : ℕ} (b : MatrixBits n) : BinMat (Fin n) :=
  fun i j => b (i,j)

def dualRank {n : ℕ} (b : MatrixBits n) : ℕ := (matrixOf b).rank

def fullIncrement (n : ℕ) (W : MatUnits (Fin n)) : MatrixBits n :=
  fun p => (W : BinMat (Fin n)) p.1 p.2

def oneIncrement (n : ℕ) (W : RankOneMat n) : MatrixBits n :=
  fun p => W.1 p.1 p.2

def fullProb (n : ℕ) (b : MatrixBits n) : ℝ := oddProb (fullIncrement n) b
def oneProb (n : ℕ) (b : MatrixBits n) : ℝ := oddProb (oneIncrement n) b
def sharpConstant (n : ℕ) : ℝ := VPVNP.sharpRatio ((2:ℝ)^n)

theorem q_gt_one (n : ℕ) (hn : 0 < n) : 1 < (2:ℝ)^n :=
  one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)

theorem sharp_constant_formula (n : ℕ) :
    sharpConstant n = 2*(1-1/(2:ℝ)^n) := by
  have hp : (2:ℝ)^n ≠ 0 := by positivity
  unfold sharpConstant VPVNP.sharpRatio
  field_simp [hp] <;> ring

theorem full_card_pos (n : ℕ) : 0 < Fintype.card (MatUnits (Fin n)) :=
  Fintype.card_pos_iff.mpr ⟨1⟩

theorem one_card_pos (n : ℕ) (hn : 0 < n) : 0 < Fintype.card (RankOneMat n) :=
  Fintype.card_pos_iff.mpr ⟨⟨tailMatrix n 1, tailMatrix_rank n 1 (by omega)⟩⟩

theorem dual_rank_le {n : ℕ} (b : MatrixBits n) : dualRank b ≤ n :=
  (matrixOf b).rank_le_width

theorem dual_rank_pos {n : ℕ} (b : MatrixBits n) (hb : b ≠ 0) : 0 < dualRank b := by
  by_contra h
  have hz : (matrixOf b).rank = 0 := by
    change ¬ 0 < (matrixOf b).rank at h
    omega
  have hm := matrix_rank_zero_imp_zero (matrixOf b) hz
  apply hb
  funext p
  change matrixOf b p.1 p.2 = 0
  rw [hm]
  rfl

theorem full_prob_formula (n : ℕ) (b : MatrixBits n) :
    fullProb n b = VPVNP.fullRankProb (rankValue n (dualRank b)) := by
  change (1-entryAverage (matrixOf b))/2 = _
  rw [full_rank_entry_character]
  rfl

theorem one_prob_formula (n : ℕ) (hn : 0 < n) (b : MatrixBits n) :
    oneProb n b = VPVNP.rankOneProb ((2:ℝ)^n) ((2:ℝ)^(n-dualRank b)) := by
  change rankOneOddProb (matrixOf b) = _
  rw [rank_one_odd_formula hn]
  unfold VPVNP.rankOneProb dualRank
  ring

theorem one_prob_nonneg (n : ℕ) (hn : 0 < n) (b : MatrixBits n) :
    0 ≤ oneProb n b := oddProb_nonneg _ (one_card_pos n hn) b

theorem one_prob_pos (n : ℕ) (hn : 0 < n) (b : MatrixBits n) (hb : b ≠ 0) :
    0 < oneProb n b := by
  rw [one_prob_formula n hn]
  exact (VPVNP.floorOne_pos (q_gt_one n hn)).trans_le
    (VPVNP.rank_one_floor (q_gt_one n hn) (rank_kernel_half n _ (dual_rank_pos b hb)))

theorem probability_bound (n : ℕ) (hn : 0 < n) (b : MatrixBits n) :
    fullProb n b ≤ sharpConstant n * oneProb n b := by
  by_cases hb : b=0
  · subst b
    unfold fullProb oneProb
    rw [oddProb_zero _ (full_card_pos n), oddProb_zero _ (one_card_pos n hn),mul_zero]
  · rw [full_prob_formula,one_prob_formula n hn]
    exact VPVNP.rank_pointwise (q_gt_one n hn)
      (rank_kernel_half n _ (dual_rank_pos b hb))
      (rankValue_lower n _ (dual_rank_pos b hb) (dual_rank_le b))

theorem probability_gap (n : ℕ) (hn : 0 < n) (b : MatrixBits n)
    (hb : 2 ≤ dualRank b) :
    fullProb n b ≤ (2*sharpConstant n/3) * oneProb n b := by
  rw [full_prob_formula,one_prob_formula n hn]
  exact VPVNP.rank_nonextremal (q_gt_one n hn)
    (rank_kernel_quarter n _ hb (dual_rank_le b))
    (rankValue_lower n _ (by omega) (dual_rank_le b))

theorem probability_attains (n : ℕ) (hn : 0 < n) (b : MatrixBits n)
    (hb : dualRank b=1) :
    fullProb n b = sharpConstant n * oneProb n b := by
  rw [full_prob_formula,one_prob_formula n hn,hb,rankValue_one n hn,two_pow_half n hn]
  exact VPVNP.rank_one_attains (q_gt_one n hn)

section Observer
variable {J : Type*} [Fintype J]

def fullEnergy (n : ℕ) (f : MatrixBits n → J → ℝ) : ℝ :=
  vectorEnergy (fullIncrement n) f

def oneEnergy (n : ℕ) (f : MatrixBits n → J → ℝ) : ℝ :=
  vectorEnergy (oneIncrement n) f

def highRankEnergy (n : ℕ) (f : MatrixBits n → J → ℝ) : ℝ :=
  4*∑ b : MatrixBits n, if 2 ≤ dualRank b then observerWeight f b * oneProb n b else 0

theorem full_energy_spectral (n : ℕ) (f : MatrixBits n → J → ℝ) :
    fullEnergy n f = 4*∑ b : MatrixBits n, observerWeight f b * fullProb n b :=
  vector_energy_spectral _ (full_card_pos n) f

theorem one_energy_spectral (n : ℕ) (hn : 0 < n) (f : MatrixBits n → J → ℝ) :
    oneEnergy n f = 4*∑ b : MatrixBits n, observerWeight f b * oneProb n b :=
  vector_energy_spectral _ (one_card_pos n hn) f

theorem one_energy_positive (n : ℕ) (hn : 0 < n) (f : MatrixBits n → J → ℝ)
    (hf : ∃ a a', f a ≠ f a') : 0 < oneEnergy n f := by
  obtain ⟨b,hb,hw⟩ := nonconstant_has_mode f hf
  rw [one_energy_spectral n hn]
  have hsum : 0 < ∑ a : MatrixBits n, observerWeight f a * oneProb n a :=
    (mul_pos hw (one_prob_pos n hn b hb)).trans_le
      (Finset.single_le_sum (fun a _ =>
        mul_nonneg (observer_weight_nonneg f a) (one_prob_nonneg n hn a)) (mem_univ b))
  positivity

/-- Sharp comparison of actual mean squared Euclidean changes, for every finite output. -/
theorem sharp_observer_bound (n : ℕ) (hn : 0 < n) (f : MatrixBits n → J → ℝ) :
    fullEnergy n f ≤ sharpConstant n * oneEnergy n f := by
  rw [full_energy_spectral,one_energy_spectral n hn]
  have h := VPVNP.weighted_bound (observerWeight f) (oneProb n) (fullProb n)
    (sharpConstant n) (observer_weight_nonneg f) (probability_bound n hn)
  convert mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤4) using 1 <;> ring

/-- Exact inequality with a deficit proportional to higher dual rank energy. -/
theorem sharp_observer_defect (n : ℕ) (hn : 0 < n) (f : MatrixBits n → J → ℝ) :
    fullEnergy n f + sharpConstant n/3 * highRankEnergy n f ≤
      sharpConstant n * oneEnergy n f := by
  rw [full_energy_spectral,one_energy_spectral n hn]
  unfold highRankEnergy
  have h := VPVNP.weighted_defect (observerWeight f) (oneProb n) (fullProb n)
    (fun b => decide (2 ≤ dualRank b)) (sharpConstant n)
    (observer_weight_nonneg f) (probability_bound n hn)
    (fun b hb => probability_gap n hn b (of_decide_eq_true hb))
  simp only [decide_eq_true_eq] at h
  convert mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤4) using 1 <;> ring

theorem sharp_observer_ratio (n : ℕ) (hn : 0 < n) (f : MatrixBits n → J → ℝ)
    (hf : ∃ a a', f a ≠ f a') :
    fullEnergy n f / oneEnergy n f ≤ sharpConstant n :=
  (div_le_iff₀ (one_energy_positive n hn f hf)).2 (sharp_observer_bound n hn f)

theorem strict_observer_contraction (n : ℕ) (hn : 2 ≤ n) (f : MatrixBits n → J → ℝ)
    (hf : ∃ a a', f a ≠ f a') :
    fullEnergy n f / oneEnergy n f < (n:ℝ) := by
  have hp : 0 < n := by omega
  have h := sharp_observer_ratio n hp f hf
  have hc : sharpConstant n < 2 := VPVNP.sharp_lt_two (q_gt_one n hp)
  exact h.trans_lt (hc.trans_le (by exact_mod_cast hn))

/-- Near-saturation bounds the denominator-weighted energy in rank >=2 modes. -/
theorem observer_stability (n : ℕ) (hn : 0 < n) (f : MatrixBits n → J → ℝ)
    (hf : ∃ a a', f a ≠ f a') (epsilon : ℝ)
    (hnear : sharpConstant n*(1-epsilon) ≤ fullEnergy n f / oneEnergy n f) :
    highRankEnergy n f / oneEnergy n f ≤ 3*epsilon := by
  have hp := one_energy_positive n hn f hf
  have hc : 0 < sharpConstant n := VPVNP.sharp_pos (q_gt_one n hn)
  have hh := (le_div_iff₀ hp).1 hnear
  have hd := sharp_observer_defect n hn f
  have hmul : sharpConstant n/3 * highRankEnergy n f ≤
      (sharpConstant n/3)*(3*epsilon*oneEnergy n f) := by nlinarith only [hh,hd]
  apply (div_le_iff₀ hp).2
  exact (mul_le_mul_left₀ (show 0 < sharpConstant n/3 by positivity)).1 hmul

end Observer

/-- A single rank-one character attains the sharp bound (scalar output). -/
theorem sharp_observer_attained (n : ℕ) (hn : 0 < n) :
    ∃ f : MatrixBits n → Unit → ℝ, 0 < oneEnergy n f ∧
      fullEnergy n f / oneEnergy n f = sharpConstant n := by
  let b : MatrixBits n := fun p => tailMatrix n 1 p.1 p.2
  have hr : dualRank b = 1 := tailMatrix_rank n 1 (by omega)
  have hb : b ≠ 0 := by
    intro h
    have hz : matrixOf b = 0 := by rw [h]; rfl
    change (matrixOf b).rank = 1 at hr
    rw [hz,Matrix.rank_zero] at hr
    omega
  refine ⟨characterObserver b,?_,?_⟩
  have h1 : oneEnergy n (characterObserver b) = 4*oneProb n b :=
    character_energy _ (one_card_pos n hn) b
  have h2 : fullEnergy n (characterObserver b) = 4*fullProb n b :=
    character_energy _ (full_card_pos n) b
  have hp := one_prob_pos n hn b hb
  · rw [h1]
    positivity
  · rw [h1,h2,probability_attains n hn b hr]
    field_simp [hp.ne'] <;> ring

end
end VPVNP.Binary

#print axioms VPVNP.Binary.scalar_energy_spectral
#print axioms VPVNP.Binary.vector_energy_mean
#print axioms VPVNP.Binary.vector_energy_spectral
#print axioms VPVNP.Binary.nonconstant_has_mode
#print axioms VPVNP.Binary.character_energy
#print axioms VPVNP.Binary.rankValue_abs_le_one
#print axioms VPVNP.Binary.rankValue_lower
#print axioms VPVNP.Binary.full_prob_formula
#print axioms VPVNP.Binary.one_prob_formula
#print axioms VPVNP.Binary.probability_bound
#print axioms VPVNP.Binary.probability_gap
#print axioms VPVNP.Binary.probability_attains
#print axioms VPVNP.Binary.one_energy_positive
#print axioms VPVNP.Binary.sharp_constant_formula
#print axioms VPVNP.Binary.sharp_observer_bound
#print axioms VPVNP.Binary.sharp_observer_defect
#print axioms VPVNP.Binary.sharp_observer_ratio
#print axioms VPVNP.Binary.strict_observer_contraction
#print axioms VPVNP.Binary.observer_stability
#print axioms VPVNP.Binary.sharp_observer_attained
