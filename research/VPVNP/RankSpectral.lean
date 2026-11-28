import Mathlib

/-!
VPVNP-02B: finite orthogonal expansion and rank-conditioned observer bounds.

The orthogonality and reconstruction hypotheses below are explicit. The
matrix-specific GL character counts are a separate VPVNP-02C obligation.
-/

open scoped BigOperators
open Finset

namespace VPVNP

section Orthogonal

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- Unnormalized Parseval for an explicitly orthogonal character family. -/
theorem orthogonal_energy (chi : B → A → ℝ) (u : B → ℝ)
    (horth : ∀ b c : B, (∑ a : A, chi b a * chi c a) =
      if b = c then (Fintype.card A : ℝ) else 0) :
    (∑ a : A, (∑ b : B, u b * chi b a) ^ 2) =
      (Fintype.card A : ℝ) * ∑ b : B, (u b)^2 := by
  classical
  calc
    (∑ a : A, (∑ b : B, u b * chi b a)^2) =
        ∑ a : A, ∑ b : B, ∑ c : B, (u b * u c) * (chi b a * chi c a) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [pow_two, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          ring
    _ = ∑ b : B, ∑ c : B, (u b * u c) * ∑ a : A, chi b a * chi c a := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.mul_sum]
    _ = ∑ b : B, ∑ c : B, (u b * u c) *
        (if b = c then (Fintype.card A : ℝ) else 0) := by
          simp_rw [horth]
    _ = ∑ b : B, (u b * u b) * (Fintype.card A : ℝ) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_eq_single b]
          · simp
          · intro c hc hcb
            simp [Ne.symm hcb]
          · simp
    _ = (Fintype.card A : ℝ) * ∑ b : B, (u b)^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring

/-- Exact energy of a shift in any reconstructed multiplicative-character expansion. -/
theorem shift_energy [Add A] (chi : B → A → ℝ) (f : A → ℝ) (u : B → ℝ)
    (horth : ∀ b c : B, (∑ a : A, chi b a * chi c a) =
      if b = c then (Fintype.card A : ℝ) else 0)
    (hchar : ∀ b a w, chi b (a + w) = chi b a * chi b w)
    (hrecon : ∀ a, f a = ∑ b : B, u b * chi b a) (w : A) :
    (∑ a : A, (f (a + w) - f a)^2) =
      (Fintype.card A : ℝ) * ∑ b : B, (u b * (chi b w - 1))^2 := by
  have hdiff : ∀ a : A, f (a+w) - f a =
      ∑ b : B, (u b * (chi b w - 1)) * chi b a := by
    intro a
    rw [hrecon (a+w), hrecon a, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [hchar]
    ring
  simp_rw [hdiff]
  exact orthogonal_energy chi (fun b => u b * (chi b w - 1)) horth

/-- For a sign character the shift multiplier is exactly zero or four. -/
theorem sign_energy (x : ℝ) (hx : x = 1 ∨ x = -1) :
    (x - 1)^2 = if x = -1 then 4 else 0 := by
  rcases hx with h | h <;> rw [h] <;> norm_num

end Orthogonal

section Weighted

variable {B : Type*} [Fintype B]

/-- Nonnegative spectral mixtures preserve a componentwise comparison. -/
theorem weighted_bound (w p t : B → ℝ) (C : ℝ)
    (hw : ∀ b, 0 ≤ w b) (h : ∀ b, t b ≤ C * p b) :
    (∑ b, w b * t b) ≤ C * ∑ b, w b * p b := by
  calc
    (∑ b, w b * t b) ≤ ∑ b, w b * (C * p b) := by
      exact Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (h b) (hw b))
    _ = C * ∑ b, w b * p b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

theorem weighted_ratio (w p t : B → ℝ) (C : ℝ)
    (hw : ∀ b, 0 ≤ w b) (h : ∀ b, t b ≤ C * p b)
    (hpos : 0 < ∑ b, w b * p b) :
    (∑ b, w b * t b) / (∑ b, w b * p b) ≤ C :=
  (div_le_iff₀ hpos).2 (weighted_bound w p t C hw h)

/-- A spectral gap away from the extremal stratum forces concentration.
The bad indicator measures energy weighted by the denominator response. -/
theorem weighted_defect (w p t : B → ℝ) (bad : B → Bool) (C : ℝ)
    (hw : ∀ b, 0 ≤ w b) (h : ∀ b, t b ≤ C * p b)
    (hbad : ∀ b, bad b = true → t b ≤ (2*C/3) * p b) :
    (∑ b, w b * t b) + C/3 * (∑ b, if bad b then w b * p b else 0)
      ≤ C * ∑ b, w b * p b := by
  have hlocal : ∀ b, w b * t b + C/3 * (if bad b then w b * p b else 0)
      ≤ C * (w b * p b) := by
    intro b
    cases hb : bad b with
    | false =>
      simp only [hb, Bool.false_eq_true, if_false, mul_zero, add_zero]
      calc
        w b * t b ≤ w b * (C * p b) := mul_le_mul_of_nonneg_left (h b) (hw b)
        _ = C * (w b * p b) := by ring
    | true =>
      simp only [hb, if_true]
      have hh := mul_le_mul_of_nonneg_left (hbad b hb) (hw b)
      linarith only [hh, show w b * ((2*C/3)*p b) + C/3*(w b*p b) =
        C*(w b*p b) by ring]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum (fun b _ => hlocal b)

/-- Explicit attainment by a single spectral mode. -/
theorem singleton_ratio [DecidableEq B] (p t : B → ℝ) (b₀ : B)
    (C : ℝ) (hp : 0 < p b₀) (heq : t b₀ = C * p b₀) :
    (∑ b : B, (if b = b₀ then (1:ℝ) else 0) * t b) /
      (∑ b : B, (if b = b₀ then (1:ℝ) else 0) * p b) = C := by
  classical
  have hs (g : B → ℝ) :
      (∑ b : B, (if b = b₀ then (1:ℝ) else 0) * g b) = g b₀ := by
    rw [Finset.sum_eq_single b₀]
    · simp
    · intro b hb hne
      simp [hne]
    · simp
  rw [hs t, hs p, heq]
  exact (div_eq_iff (ne_of_gt hp)).2 rfl

end Weighted

section Rank

/-- q denotes 2^n, and z denotes 2^(n-k). -/
noncomputable def rankOneProb (q z : ℝ) : ℝ := (q-z)*q/(2*(q-1)^2)

noncomputable def fullRankProb (c : ℝ) : ℝ := (1-c)/2

noncomputable def floorOne (q : ℝ) : ℝ := q^2/(4*(q-1)^2)
noncomputable def ceilFull (q : ℝ) : ℝ := q/(2*(q-1))
noncomputable def sharpRatio (q : ℝ) : ℝ := 2*(q-1)/q

theorem floorOne_pos {q : ℝ} (hq : 1 < q) : 0 < floorOne q := by
  unfold floorOne
  positivity

theorem rank_one_floor {q z : ℝ} (hq : 1 < q) (hz : z ≤ q/2) :
    floorOne q ≤ rankOneProb q z := by
  unfold floorOne rankOneProb
  have hpos : 0 < 2*(q-1)^2 := by positivity
  have hnum : q^2/2 ≤ (q-z)*q := by
    have hh := mul_le_mul_of_nonneg_right hz (show 0 ≤ q by linarith)
    nlinarith
  calc
    q^2/(4*(q-1)^2) = (q^2/2)/(2*(q-1)^2) := by
      field_simp
      <;> ring
    _ ≤ (q-z)*q/(2*(q-1)^2) :=
      div_le_div_of_nonneg_right hnum hpos.le

theorem rank_two_floor {q z : ℝ} (hq : 1 < q) (hz : z ≤ q/4) :
    (3/2) * floorOne q ≤ rankOneProb q z := by
  unfold floorOne rankOneProb
  have hpos : 0 < 2*(q-1)^2 := by positivity
  have hnum : 3*q^2/4 ≤ (q-z)*q := by
    have hh := mul_le_mul_of_nonneg_right hz (show 0 ≤ q by linarith)
    nlinarith
  calc
    (3/2)*(q^2/(4*(q-1)^2)) = (3*q^2/4)/(2*(q-1)^2) := by
      field_simp
      <;> ring
    _ ≤ (q-z)*q/(2*(q-1)^2) :=
      div_le_div_of_nonneg_right hnum hpos.le

theorem full_rank_ceil {q c : ℝ} (hq : 1 < q) (hc : -(1/(q-1)) ≤ c) :
    fullRankProb c ≤ ceilFull q := by
  have hq' : q-1 ≠ 0 := by linarith
  have heq : (1+1/(q-1))/2 = ceilFull q := by
    unfold ceilFull
    field_simp
    <;> ring
  unfold fullRankProb
  rw [← heq]
  linarith

theorem sharp_product {q : ℝ} (hq : 1 < q) :
    sharpRatio q * floorOne q = ceilFull q := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q-1 ≠ 0 := by linarith
  unfold sharpRatio floorOne ceilFull
  field_simp
  <;> ring

theorem sharp_pos {q : ℝ} (hq : 1 < q) : 0 < sharpRatio q := by
  unfold sharpRatio
  positivity

theorem sharp_lt_two {q : ℝ} (hq : 1 < q) : sharpRatio q < 2 := by
  unfold sharpRatio
  apply (div_lt_iff₀ (show 0 < q by linarith)).2
  linarith

/-- Conditional pointwise bound using the finite-character count inequalities. -/
theorem rank_pointwise {q z c : ℝ} (hq : 1 < q)
    (hz : z ≤ q/2) (hc : -(1/(q-1)) ≤ c) :
    fullRankProb c ≤ sharpRatio q * rankOneProb q z := by
  calc
    fullRankProb c ≤ ceilFull q := full_rank_ceil hq hc
    _ = sharpRatio q * floorOne q := (sharp_product hq).symm
    _ ≤ sharpRatio q * rankOneProb q z :=
      mul_le_mul_of_nonneg_left (rank_one_floor hq hz) (sharp_pos hq).le

/-- Higher dual ranks have a uniform relative gap of at least one third. -/
theorem rank_nonextremal {q z c : ℝ} (hq : 1 < q)
    (hz : z ≤ q/4) (hc : -(1/(q-1)) ≤ c) :
    fullRankProb c ≤ (2*sharpRatio q/3) * rankOneProb q z := by
  have h := mul_le_mul_of_nonneg_left (rank_two_floor hq hz)
    (show 0 ≤ 2*sharpRatio q/3 by have := sharp_pos hq; positivity)
  calc
    fullRankProb c ≤ ceilFull q := full_rank_ceil hq hc
    _ = (2*sharpRatio q/3) * ((3/2)*floorOne q) := by
      rw [← sharp_product hq]
      ring
    _ ≤ (2*sharpRatio q/3) * rankOneProb q z := h

/-- Formula-level equality in the rank-one mode. -/
theorem rank_one_attains {q : ℝ} (hq : 1 < q) :
    fullRankProb (-(1/(q-1))) = sharpRatio q * rankOneProb q (q/2) := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q-1 ≠ 0 := by linarith
  unfold fullRankProb sharpRatio rankOneProb
  field_simp
  <;> ring

end Rank

end VPVNP

#print axioms VPVNP.orthogonal_energy
#print axioms VPVNP.shift_energy
#print axioms VPVNP.sign_energy
#print axioms VPVNP.weighted_bound
#print axioms VPVNP.weighted_ratio
#print axioms VPVNP.weighted_defect
#print axioms VPVNP.singleton_ratio
#print axioms VPVNP.rank_one_floor
#print axioms VPVNP.rank_two_floor
#print axioms VPVNP.full_rank_ceil
#print axioms VPVNP.rank_pointwise
#print axioms VPVNP.rank_nonextremal
#print axioms VPVNP.rank_one_attains
#print axioms VPVNP.sharp_lt_two
