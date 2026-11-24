import Mathlib

/-!
Independent scalar assembly certificates for the valuation export traced in
RH26B14_AUX3_EXPORT.md. The stronger supplier inequalities in the refined
assembly are explicit premises. No arithmetic realization is assumed.
-/

namespace RH26E05C1

noncomputable section

def scale (C H : ℝ) : ℝ := (C + 1)^2 * H^18

def rhoOriginal : ℝ := 1164022 / 4000000

def rhoRefined : ℝ := 11042 / 4000000

def originalEnvelope (C : ℝ) : ℝ :=
  1000 * (C + 1)^3 + 12 * C + rhoOriginal

def refinedEnvelope (C : ℝ) : ℝ :=
  104 * (C + 1)^3 + (73 / 36 : ℝ) * C + rhoRefined

structure Costs where
  gen : ℝ
  small23 : ℝ
  ramified : ℝ
  genericSmall : ℝ
  exceptional : ℝ
  globalCorrection : ℝ

def total (t : Costs) : ℝ :=
  t.gen + t.small23 + t.ramified + t.genericSmall +
    t.exceptional + t.globalCorrection

def OriginalBounds (C X H : ℝ) (t : Costs) : Prop :=
  t.gen ≤ 2 * scale C H ∧
  t.small23 ≤ 8 * C * X ∧
  t.ramified ≤ 4 * C * X ∧
  t.genericSmall ≤ 1000 * (C + 1)^3 * X ∧
  t.exceptional ≤ 1164000 * scale C H ∧
  t.globalCorrection ≤ 20 * scale C H

def RefinedBounds (C X H : ℝ) (t : Costs) : Prop :=
  t.gen ≤ 2 * scale C H ∧
  t.small23 ≤ 2 * C * X ∧
  t.ramified ≤ (C / 36) * X ∧
  t.genericSmall ≤ 104 * (C + 1)^3 * X ∧
  t.exceptional ≤ 11020 * scale C H ∧
  t.globalCorrection ≤ 20 * scale C H

theorem scale_nonneg (C H : ℝ) : 0 ≤ scale C H := by
  unfold scale
  positivity

theorem original_absorption (C H b X : ℝ)
    (hscale : 4000000 * scale C H ≤ b) (hb : b ≤ X) :
    1164022 * scale C H ≤ rhoOriginal * X := by
  have h := mul_le_mul_of_nonneg_left (hscale.trans hb)
    (show 0 ≤ rhoOriginal by norm_num [rhoOriginal])
  calc
    _ = rhoOriginal * (4000000 * scale C H) := by unfold rhoOriginal; ring
    _ ≤ _ := h

theorem refined_absorption (C H b X : ℝ)
    (hscale : 4000000 * scale C H ≤ b) (hb : b ≤ X) :
    11042 * scale C H ≤ rhoRefined * X := by
  have h := mul_le_mul_of_nonneg_left (hscale.trans hb)
    (show 0 ≤ rhoRefined by norm_num [rhoRefined])
  calc
    _ = rhoRefined * (4000000 * scale C H) := by unfold rhoRefined; ring
    _ ≤ _ := h

theorem original_gap_identity (C : ℝ) :
    2 * (C + 1)^3 - 12 * C =
      2 * C^3 + 6 * (C - 1/2)^2 + 1/2 := by
  ring

theorem original_envelope (C : ℝ) (hC : 0 ≤ C) :
    originalEnvelope C ≤ 1002 * (C + 1)^3 := by
  have hg := original_gap_identity C
  have hc3 : 0 ≤ C^3 := pow_nonneg hC 3
  have hs : 0 ≤ (C - 1/2)^2 := sq_nonneg _
  unfold originalEnvelope rhoOriginal
  nlinarith only [hg, hc3, hs]

theorem original_integer_minimum (K : ℕ) :
    (∀ C : ℝ, 0 ≤ C → originalEnvelope C ≤ (K : ℝ) * (C + 1)^3) ↔
      1002 ≤ K := by
  constructor
  · intro h
    by_contra hn
    have hk : K ≤ 1001 := by omega
    have hk' : (K : ℝ) ≤ 1001 := by exact_mod_cast hk
    have htest := h (1/2) (by norm_num)
    norm_num [originalEnvelope, rhoOriginal] at htest
    linarith only [htest, hk']
  · intro hk C hC
    have hk' : (1002 : ℝ) ≤ K := by exact_mod_cast hk
    exact (original_envelope C hC).trans
      (mul_le_mul_of_nonneg_right hk' (pow_nonneg (by linarith) 3))

theorem refined_gap_identity (C : ℝ) :
    4 * (C + 1)^3 - 27 * C = (2 * C - 1)^2 * (C + 4) := by
  ring

theorem refined_envelope (C : ℝ) (hC : 0 ≤ C) :
    refinedEnvelope C ≤ 105 * (C + 1)^3 := by
  have hs : 0 ≤ (2 * C - 1)^2 * (C + 4) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hratio : 27 * C ≤ 4 * (C + 1)^3 := by
    linarith only [refined_gap_identity C, hs]
  have hCub : 1 ≤ (C + 1)^3 := one_le_pow₀ (by linarith) (n := 3)
  unfold refinedEnvelope rhoRefined
  nlinarith only [hratio, hCub]

theorem refined_integer_minimum (K : ℕ) :
    (∀ C : ℝ, 0 ≤ C → refinedEnvelope C ≤ (K : ℝ) * (C + 1)^3) ↔
      105 ≤ K := by
  constructor
  · intro h
    by_contra hn
    have hk : K ≤ 104 := by omega
    have hk' : (K : ℝ) ≤ 104 := by exact_mod_cast hk
    have htest := h (1/2) (by norm_num)
    norm_num [refinedEnvelope, rhoRefined] at htest
    linarith only [htest, hk']
  · intro hk C hC
    have hk' : (105 : ℝ) ≤ K := by exact_mod_cast hk
    exact (refined_envelope C hC).trans
      (mul_le_mul_of_nonneg_right hk' (pow_nonneg (by linarith) 3))

theorem original_assembly (C H b X Y : ℝ) (t : Costs)
    (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hscale : 4000000 * scale C H ≤ b) (hb : b ≤ X)
    (hY : Y ≤ total t) (ht : OriginalBounds C X H t) :
    Y ≤ 1002 * (C + 1)^3 * X := by
  obtain ⟨hg, h23, hqd, hs, he, hc⟩ := ht
  have ha := original_absorption C H b X hscale hb
  have hmid : Y ≤ originalEnvelope C * X := by
    unfold total at hY
    unfold originalEnvelope
    nlinarith only [hY, hg, h23, hqd, hs, he, hc, ha]
  exact hmid.trans (mul_le_mul_of_nonneg_right (original_envelope C hC) hX)

theorem refined_assembly (C H b X Y : ℝ) (t : Costs)
    (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hscale : 4000000 * scale C H ≤ b) (hb : b ≤ X)
    (hY : Y ≤ total t) (ht : RefinedBounds C X H t) :
    Y ≤ 105 * (C + 1)^3 * X := by
  obtain ⟨hg, h23, hqd, hs, he, hc⟩ := ht
  have ha := refined_absorption C H b X hscale hb
  have hmid : Y ≤ refinedEnvelope C * X := by
    unfold total at hY
    unfold refinedEnvelope
    nlinarith only [hY, hg, h23, hqd, hs, he, hc, ha]
  exact hmid.trans (mul_le_mul_of_nonneg_right (refined_envelope C hC) hX)

theorem export_propagation (eta R Y V K X N : ℝ)
    (hEta : eta ≤ R * (Y + V)) (hY : Y ≤ K * X)
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hN : 0 ≤ N) :
    eta ≤ R * (K * (X + N) + V) := by
  have hKN : 0 ≤ K * N := mul_nonneg hK hN
  have hpad : K * X ≤ K * (X + N) := by linarith only [hKN]
  have hadd : Y + V ≤ K * (X + N) + V := by
    linarith only [hY, hpad]
  exact hEta.trans (mul_le_mul_of_nonneg_left hadd hR)

theorem missing_scale_control :
    ∃ (C H b X Y : ℝ) (t : Costs),
      0 < C ∧ 0 < H ∧ 0 < b ∧ 0 < X ∧ b ≤ X ∧
      Y ≤ total t ∧ OriginalBounds C X H t ∧
      b < 4000000 * scale C H ∧
      1002 * (C + 1)^3 * X < Y := by
  refine ⟨1, 2, 1, 1, 1164000 * scale 1 2,
    ⟨0, 0, 0, 0, 1164000 * scale 1 2, 0⟩, ?_⟩
  norm_num [total, OriginalBounds, scale]

theorem negative_rank_control :
    ∃ (eta R Y V K X N : ℝ),
      eta ≤ R * (Y + V) ∧ Y ≤ K * X ∧ 0 ≤ K ∧ 0 ≤ N ∧
      R < 0 ∧ R * (K * (X + N) + V) < eta := by
  refine ⟨0, -1, 0, 0, 1, 1, 0, ?_⟩
  norm_num

theorem negative_padding_control :
    ∃ (eta R Y V K X N : ℝ),
      eta ≤ R * (Y + V) ∧ Y ≤ K * X ∧ 0 ≤ R ∧ 0 ≤ K ∧
      N < 0 ∧ R * (K * (X + N) + V) < eta := by
  refine ⟨1, 1, 1, 0, 1, 1, -1, ?_⟩
  norm_num

end

end RH26E05C1

#print axioms RH26E05C1.scale_nonneg
#print axioms RH26E05C1.original_absorption
#print axioms RH26E05C1.refined_absorption
#print axioms RH26E05C1.original_gap_identity
#print axioms RH26E05C1.original_envelope
#print axioms RH26E05C1.original_integer_minimum
#print axioms RH26E05C1.refined_gap_identity
#print axioms RH26E05C1.refined_envelope
#print axioms RH26E05C1.refined_integer_minimum
#print axioms RH26E05C1.original_assembly
#print axioms RH26E05C1.refined_assembly
#print axioms RH26E05C1.export_propagation
#print axioms RH26E05C1.missing_scale_control
#print axioms RH26E05C1.negative_rank_control
#print axioms RH26E05C1.negative_padding_control
