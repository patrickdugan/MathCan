import Mathlib

/-!
Independent exceptional-prime scalar certificates extracted from the
RH26B11/B12 source inventory. All arithmetic scale and local cost
premises are explicit. No upstream arithmetic realization is imported.
-/

namespace RH26E05C3

open scoped BigOperators

theorem cutoff_ratio (s D m b : ℝ) (hs : 0 < s) (hm : 0 < m)
    (htie : s * D = m * b) : b / s = D / m := by
  field_simp [hs.ne', hm.ne'] <;> nlinarith only [htie]

theorem denominator_envelope (H D : ℝ) (hH : 1 ≤ H)
    (hD : D ≤ 4*H^7+6*H^4) : D ≤ 10*H^7 := by
  have hp : H^4 ≤ H^7 := pow_le_pow_right₀ hH (by norm_num)
  linarith only [hD, hp]

theorem exceptional_divisions (H m D s l b hB : ℝ)
    (hH : 1 ≤ H) (hm : 2 ≤ m) (hD0 : 0 ≤ D) (hD : D ≤ 10*H^7)
    (hs : 0 < s) (hsl : s ≤ l) (hl : 8 ≤ l)
    (hb : 0 ≤ b) (hB0 : 0 ≤ hB) (hB2 : hB ≤ 2*b)
    (htie : s*D = m*b) :
    hB/l ≤ 10*H^7 ∧ hB/l^2 ≤ (5/4)*H^7 := by
  have hm0 : 0 < m := by linarith
  have hl0 : 0 < l := by linarith
  have hr := cutoff_ratio s D m b hs hm0 htie
  have h1 : hB/l ≤ 10*H^7 := by
    calc
      _ ≤ hB/s := div_le_div_of_nonneg_left hB0 hs hsl
      _ ≤ (2*b)/s := div_le_div_of_nonneg_right hB2 hs.le
      _ = 2*(b/s) := by ring
      _ = 2*(D/m) := by rw [hr]
      _ ≤ D := by
        rw [← mul_div_assoc, div_le_iff₀ hm0]
        nlinarith only [mul_nonneg hD0 (sub_nonneg.mpr hm)]
      _ ≤ _ := hD
  refine ⟨h1, ?_⟩
  calc
    hB/l^2 = (hB/l)/l := by ring
    _ ≤ (hB/l)/8 :=
      div_le_div_of_nonneg_left (div_nonneg hB0 hl0.le) (by norm_num) hl
    _ ≤ (10*H^7)/8 := div_le_div_of_nonneg_right h1 (by norm_num)
    _ = _ := by ring

theorem ep_bound (H C u v : ℝ) (hH : 1 ≤ H) (hC : 0 ≤ C)
    (hu : u ≤ 10*H^7) (hv : v ≤ H+1) :
    C*(1+u+v) ≤ 13*C*H^7 := by
  have hH7 : H ≤ H^7 := by
    calc
      H = H^1 := (pow_one H).symm
      _ ≤ _ := pow_le_pow_right₀ hH (by norm_num)
  have hone : 1 ≤ H^7 := one_le_pow₀ hH
  have hh : 1+u+v ≤ 13*H^7 := by linarith only [hu, hv, hH7, hone]
  calc
    _ ≤ C*(13*H^7) := mul_le_mul_of_nonneg_left hh hC
    _ = _ := by ring

theorem flat_bound (H l w Sc g eta band : ℝ)
    (hH : 1 ≤ H) (hl : 0 < l) (hw : w ≤ 9*l)
    (hSc : Sc ≤ 4*H) (hg : g ≤ H)
    (heta0 : 0 ≤ eta) (heta : eta ≤ 4*H) (hband : band ≤ 1) :
    w/l+Sc+g+eta*band ≤ 18*H^7 := by
  have hH7 : H ≤ H^7 := by
    calc
      H = H^1 := (pow_one H).symm
      _ ≤ _ := pow_le_pow_right₀ hH (by norm_num)
  have hone : 1 ≤ H^7 := one_le_pow₀ hH
  have hwd : w/l ≤ 9 := (div_le_iff₀ hl).2 hw
  have he := mul_le_mul_of_nonneg_left hband heta0
  linarith only [hwd, hSc, hg, he, heta, hH7, hone]

theorem bb_bound (H C f n t nV g : ℝ)
    (hH : 1 ≤ H) (hC : 0 ≤ C) (hf0 : 0 ≤ f) (hn0 : 0 ≤ n)
    (ht0 : 0 ≤ t) (hnV0 : 0 ≤ nV) (hg0 : 0 ≤ g)
    (hf : f ≤ 2*H) (hn : n ≤ H) (ht : t ≤ H)
    (hnV : nV ≤ 4*H^2) (hg : g ≤ H) :
    C*f*n*t^2*nV*g^2 ≤ 8*C*H^9 := by
  have hH0 : 0 ≤ H := by linarith
  have hp : H^8 ≤ H^9 := pow_le_pow_right₀ hH (by norm_num)
  calc
    _ ≤ C*(2*H)*H*H^2*(4*H^2)*H^2 := by
      gcongr <;> first | assumption | positivity | linarith
    _ = 8*C*H^8 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem split_length (H C f m e : ℝ)
    (hH : 1 ≤ H) (hC : 0 ≤ C) (hf0 : 0 ≤ f)
    (hm0 : 0 ≤ m) (he0 : 0 ≤ e)
    (hf : f ≤ 2*H) (hm : m ≤ H) (he : e ≤ 13*C*H^7) :
    (2*f*m+f)*e ≤ 78*C*H^9 := by
  have hH0 : 0 ≤ H := by linarith
  have hh : H ≤ H^2 := by
    calc
      H = H^1 := (pow_one H).symm
      _ ≤ _ := pow_le_pow_right₀ hH (by norm_num)
  have hfm := mul_le_mul hf hm hm0 (by positivity : 0 ≤ 2*H)
  have hf6 : 2*f*m+f ≤ 6*H^2 := by nlinarith only [hfm, hf, hh]
  calc
    _ ≤ (6*H^2)*(13*C*H^7) := mul_le_mul hf6 he he0 (by positivity)
    _ = _ := by ring

theorem inert_length (H C f r m h flat e : ℝ)
    (hH : 1 ≤ H) (hC : 0 ≤ C) (hf0 : 0 ≤ f)
    (hr0 : 0 ≤ r) (hm0 : 0 ≤ m) (hh0 : 0 ≤ h)
    (hflat0 : 0 ≤ flat) (he0 : 0 ≤ e)
    (hf : f ≤ 2*H) (hr : r ≤ 2*H) (hm : m ≤ H)
    (hh : h ≤ (5/4)*H^7) (hflat : flat ≤ 18*H^7)
    (he : e ≤ 13*C*H^7) :
    4*f*(C*r*(h+flat))+2*f*(C*m*e) ≤ (308*C+52*C^2)*H^9 := by
  have hH0 : 0 ≤ H := by linarith
  have hfr := mul_le_mul hf hr hr0 (by positivity : 0 ≤ 2*H)
  have hfm := mul_le_mul hf hm hm0 (by positivity : 0 ≤ 2*H)
  have hsum : h+flat ≤ (77/4)*H^7 := by linarith only [hh, hflat]
  have h1 := mul_le_mul hfr hsum (add_nonneg hh0 hflat0)
    (by positivity : 0 ≤ (2*H)*(2*H))
  have h2 := mul_le_mul hfm he he0 (by positivity : 0 ≤ (2*H)*H)
  calc
    _ = 4*C*(f*r*(h+flat))+2*C*(f*m*e) := by ring
    _ ≤ 4*C*(((2*H)*(2*H))*((77/4)*H^7))+
          2*C*(((2*H)*H)*(13*C*H^7)) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by ring

theorem exceptional_gap_identity (C : ℝ) :
    95*(C+1)^2-(316*C+52*C^2) =
      43*(C-63/43)^2+116/43 := by
  ring

theorem exceptional_envelope (C : ℝ) (hC : 0 ≤ C) :
    316*C+52*C^2 ≤ 95*(C+1)^2 := by
  have hs : 0 ≤ 43*(C-63/43)^2 := by positivity
  linarith only [exceptional_gap_identity C, hs]

theorem exceptional_integer_minimum (K : ℕ) :
    (∀ C : ℝ, 0 ≤ C → 316*C+52*C^2 ≤ (K : ℝ)*(C+1)^2) ↔
      95 ≤ K := by
  constructor
  · intro h
    by_contra hn
    have hk : K ≤ 94 := by omega
    have hk' : (K : ℝ) ≤ 94 := by exact_mod_cast hk
    have ht := h (3/2) (by norm_num)
    norm_num at ht
    linarith only [ht, hk']
  · intro hk C hC
    have hk' : (95 : ℝ) ≤ K := by exact_mod_cast hk
    exact (exceptional_envelope C hC).trans
      (mul_le_mul_of_nonneg_right hk' (sq_nonneg _))

theorem pointwise_assembly (C H bb len : ℝ) (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hbb : bb ≤ 8*C*H^9)
    (hlen : len ≤ 78*C*H^9 ∨ len ≤ (308*C+52*C^2)*H^9) :
    bb+len ≤ 95*(C+1)^2*H^9 := by
  have hH0 : 0 ≤ H := by linarith
  have hpoly : 78*C ≤ 308*C+52*C^2 := by
    nlinarith only [hC, sq_nonneg C]
  have hlen' : len ≤ (308*C+52*C^2)*H^9 := by
    rcases hlen with hs | hi
    · exact hs.trans (mul_le_mul_of_nonneg_right hpoly (pow_nonneg hH0 9))
    · exact hi
  have hsum : bb+len ≤ (316*C+52*C^2)*H^9 := by
    linarith only [hbb, hlen']
  exact hsum.trans (mul_le_mul_of_nonneg_right
    (exceptional_envelope C hC) (pow_nonneg hH0 9))

theorem count_mixed_bound (H m D s b TT Sc eta t count : ℝ)
    (hH : 2 ≤ H) (hm : 2 ≤ m) (hD0 : 0 ≤ D)
    (hD : D ≤ 4*H^7+6*H^4) (hs : 0 < s) (hb : 0 ≤ b)
    (htie : s*D=m*b) (hTT0 : 0 ≤ TT) (hTT : TT ≤ 2*H)
    (hSc0 : 0 ≤ Sc) (hSc : Sc ≤ 4*H)
    (heta0 : 0 ≤ eta) (heta : eta ≤ H)
    (ht0 : 0 ≤ t) (ht : t ≤ H)
    (hc : count ≤ (TT+2)*(Sc+3*eta+t+8*b/s+9)) :
    count ≤ (2*H+2)*(8*H+16*H^7+24*H^4+9) := by
  have hm0 : 0 < m := by linarith
  have hr := cutoff_ratio s D m b hs hm0 htie
  have hratio : 8*b/s ≤ 16*H^7+24*H^4 := by
    calc
      _ = 8*(b/s) := by ring
      _ = 8*(D/m) := by rw [hr]
      _ ≤ 4*D := by
        rw [← mul_div_assoc, div_le_iff₀ hm0]
        nlinarith only [mul_nonneg hD0 (sub_nonneg.mpr hm)]
      _ ≤ _ := by linarith only [hD]
  have hA : TT+2 ≤ 2*H+2 := by linarith only [hTT]
  have hB : Sc+3*eta+t+8*b/s+9 ≤ 8*H+16*H^7+24*H^4+9 := by
    linarith only [hSc, heta, ht, hratio]
  exact hc.trans (mul_le_mul hA hB (by positivity) (by linarith))

theorem count_envelope (H count : ℝ) (hH : 2 ≤ H)
    (hc : count ≤ (2*H+2)*(8*H+16*H^7+24*H^4+9)) :
    count ≤ 58*H^8 := by
  have hH0 : 0 ≤ H := by linarith
  have h3 : (8 : ℝ) ≤ H^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hH 3
    norm_num at h
    exact h
  have h6 : (64 : ℝ) ≤ H^6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hH 6
    norm_num at h
    exact h
  have h7 : (128 : ℝ) ≤ H^7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hH 7
    norm_num at h
    exact h
  have h8H : 8*H ≤ (1/8)*H^7 := by
    nlinarith only [mul_le_mul_of_nonneg_right h6 hH0]
  have h24 : 24*H^4 ≤ 3*H^7 := by
    nlinarith only [mul_le_mul_of_nonneg_right h3 (pow_nonneg hH0 4)]
  have h9 : (9 : ℝ) ≤ (9/128)*H^7 := by linarith only [h7]
  have hA : 2*H+2 ≤ 3*H := by linarith
  have hB : 8*H+16*H^7+24*H^4+9 ≤ (2457/128)*H^7 := by
    linarith only [h8H, h24, h9]
  calc
    _ ≤ (2*H+2)*(8*H+16*H^7+24*H^4+9) := hc
    _ ≤ (3*H)*((2457/128)*H^7) := mul_le_mul hA hB (by positivity) (by positivity)
    _ = (7371/128)*H^8 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hH0 8)

theorem prime_log_bound (H b l : ℝ) (hH : 2 ≤ H) (hb : 0 < b)
    (hl : 0 < l) (htop : l ≤ 3*b) (hlog : Real.log b ≤ H) :
    Real.log l ≤ 2*H := by
  have h := Real.log_le_log hl htop
  rw [Real.log_mul (by norm_num) hb.ne'] at h
  have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  linarith only [h, h3, hlog, hH]

theorem exceptional_sum (T : Finset ℕ) (cost : ℕ → ℝ) (C H b : ℝ)
    (hC : 0 ≤ C) (hH : 2 ≤ H) (hb : 0 < b)
    (hlog : Real.log b ≤ H) (hcard : (T.card : ℝ) ≤ 58*H^8)
    (hl : ∀ l ∈ T, 0 < (l : ℝ)) (htop : ∀ l ∈ T, (l : ℝ) ≤ 3*b)
    (hc0 : ∀ l ∈ T, 0 ≤ cost l) (hc : ∀ l ∈ T, cost l ≤ 95*(C+1)^2*H^9) :
    (∑ l ∈ T, Real.log (l : ℝ)*cost l) ≤ 11020*(C+1)^2*H^18 := by
  have hH0 : 0 ≤ H := by linarith
  have hpt : ∀ l ∈ T, Real.log (l : ℝ)*cost l ≤ 190*(C+1)^2*H^10 := by
    intro l hl'
    have h := prime_log_bound H b l hH hb (hl l hl') (htop l hl') hlog
    calc
      _ ≤ (2*H)*(95*(C+1)^2*H^9) :=
        mul_le_mul h (hc l hl') (hc0 l hl') (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ _l ∈ T, 190*(C+1)^2*H^10 := Finset.sum_le_sum hpt
    _ = (T.card : ℝ)*(190*(C+1)^2*H^10) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (58*H^8)*(190*(C+1)^2*H^10) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem exceptional_absorption (C H b : ℝ)
    (hscale : 4000000*(C+1)^2*H^18 ≤ b) :
    11020*(C+1)^2*H^18 ≤ (551/200000)*b := by
  calc
    _ = (551/200000:ℝ)*(4000000*(C+1)^2*H^18) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by norm_num)

theorem missing_scale_controls :
    ((2*(1:ℝ)+2)*(8*(1:ℝ)+16*(1:ℝ)^7+24*(1:ℝ)^4+9) = 228 ∧
      (58:ℝ)*1^8 < 228) ∧
    ∃ H m s l D b hB : ℝ,
      H=2 ∧ m=1 ∧ s=8 ∧ l=9 ∧ D=10*H^7 ∧ b=s*D ∧ hB=2*b ∧
      1 ≤ H ∧ m < 2 ∧ 0 ≤ D ∧ D ≤ 10*H^7 ∧
      0 < s ∧ s ≤ l ∧ 8 ≤ l ∧ 0 ≤ b ∧ 0 ≤ hB ∧ hB ≤ 2*b ∧
      s*D=m*b ∧ 10*H^7 < hB/l := by
  constructor
  · norm_num
  · refine ⟨2, 1, 8, 9, 1280, 10240, 20480, ?_⟩
    norm_num

end RH26E05C3

#print axioms RH26E05C3.cutoff_ratio
#print axioms RH26E05C3.denominator_envelope
#print axioms RH26E05C3.exceptional_divisions
#print axioms RH26E05C3.ep_bound
#print axioms RH26E05C3.flat_bound
#print axioms RH26E05C3.bb_bound
#print axioms RH26E05C3.split_length
#print axioms RH26E05C3.inert_length
#print axioms RH26E05C3.exceptional_gap_identity
#print axioms RH26E05C3.exceptional_envelope
#print axioms RH26E05C3.exceptional_integer_minimum
#print axioms RH26E05C3.pointwise_assembly
#print axioms RH26E05C3.count_mixed_bound
#print axioms RH26E05C3.count_envelope
#print axioms RH26E05C3.prime_log_bound
#print axioms RH26E05C3.exceptional_sum
#print axioms RH26E05C3.exceptional_absorption
#print axioms RH26E05C3.missing_scale_controls
