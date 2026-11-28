import Mathlib
import RH26E06FSplitCore

/-! Direct scalar adaptation of the pinned upstream growth-size proof
(LipschitzWeightAndMinimum.lean:64–162,282–367). E06F is imported
unchanged. The source SizeWindows cap 26 is retained as an optional
absorption premise, not an arithmetic family claim. -/
namespace RH26E06G
noncomputable section
set_option maxHeartbeats 1500000
set_option linter.unusedVariables false

def bracket (x ε : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : ℝ :=
  (nT : ℝ)*aE*(1+(m:ℝ)^2/k) +
    m*((2*(n:ℝ))*m*b*x^ε+nT2*k*b*x^ε/(n*(n*x^(-ε))))

def SizePremises (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : Prop :=
  3 ≤ x ∧ 0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ aE ≤ 2*x*b ∧
  x^(-(ε/8))*n/2 ≤ nT ∧ x^(-ε) ≤ (nT2:ℝ)/n ∧ nT2 ≤ n ∧
  x^((1:ℝ)/2-ε) ≤ m ∧ (m:ℝ) ≤ x^((1:ℝ)/2+ε/2) ∧
  x*m ≤ k ∧ k ≤ (n:ℝ)^2*x^((1:ℝ)/2-ε)

def SizeContract (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ) : Prop :=
  SizePremises C ε x n nT nT2 m b k aE ∧
    Err ≤ x^(C*ε)*bracket x ε n nT nT2 m b k aE

def GrowthIneq (x ε : ℝ) (n nT nT2 m : ℕ) (b Err G : ℝ) : Prop :=
  (nT:ℝ)*m*b*(((nT2:ℝ)/n)/2)*(G-4*x^((1:ℝ)/2+ε)) ≤ Err+2*(nT:ℝ)*m*b/x

namespace SZ

lemma rp {x : ℝ} (hx0 : 0 < x) (u v : ℝ) : x ^ (u + v) = x ^ u * x ^ v := Real.rpow_add hx0 u v

lemma nT_bound {x ε : ℝ} {n nT : ℝ} (hx0 : 0 < x) (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) :
    n ≤ 2 * nT * x ^ (ε / 8) := by
  have h8 : 0 < x ^ (ε / 8) := Real.rpow_pos_of_pos hx0 _
  have hinv : x ^ (-(ε / 8)) * x ^ (ε / 8) = 1 := by rw [← rp hx0]; simp
  have := mul_le_mul_of_nonneg_right hnT h8.le
  have e : x ^ (-(ε / 8)) * n / 2 * x ^ (ε / 8) = n / 2 := by
    calc x ^ (-(ε / 8)) * n / 2 * x ^ (ε / 8) = (x ^ (-(ε / 8)) * x ^ (ε / 8)) * n / 2 := by ring
      _ = n / 2 := by rw [hinv]; ring
  linarith

lemma T1 {x X Y m nT aE b : ℝ} (hxX : x ≤ X * m) (hXY : X ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (haE : aE ≤ 2 * x * b) : nT * aE ≤ 2 * Y * (nT * m * b) := by
  have h1 : nT * aE ≤ nT * (2 * x * b) := mul_le_mul_of_nonneg_left haE hnT0
  have h2 : 2 * x * b ≤ 2 * (Y * m) * b := by
    have : x ≤ Y * m := le_trans hxX (mul_le_mul_of_nonneg_right hXY hm0)
    nlinarith
  have h3 : nT * (2 * x * b) ≤ nT * (2 * (Y * m) * b) := mul_le_mul_of_nonneg_left h2 hnT0
  calc nT * aE ≤ nT * (2 * (Y * m) * b) := le_trans h1 h3
    _ = 2 * Y * (nT * m * b) := by ring

lemma T2 {x Y m nT aE b k : ℝ} (hx0 : 0 < x) (hY1 : 1 ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hk0 : 0 < k) (hk1 : x * m ≤ k) (haE : aE ≤ 2 * x * b) :
    nT * aE * (m ^ 2 / k) ≤ 2 * Y * (nT * m * b) := by
  have hmk : m ^ 2 / k ≤ m / x := by
    rw [div_le_div_iff₀ hk0 hx0]; nlinarith
  have h1 : nT * aE * (m ^ 2 / k) ≤ nT * (2 * x * b) * (m / x) :=
    mul_le_mul (mul_le_mul_of_nonneg_left haE hnT0) hmk (by positivity) (by positivity)
  have h2 : nT * (2 * x * b) * (m / x) = 2 * (nT * m * b) := by field_simp
  have hQ : 0 ≤ nT * m * b := by positivity
  have h3 : 2 * (nT * m * b) ≤ 2 * Y * (nT * m * b) := by nlinarith
  linarith

lemma T3 {x ε Y m n nT b : ℝ} (hx0 : 0 < x) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) (hm2 : m ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 ≤ n) :
    m * ((2 * n) * m * b * x ^ ε) ≤ 4 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hY' : x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε * x ^ (ε / 8) = Y := by
    rw [← rp hx0, ← rp hx0, hY]; ring_nf
  have hmY : m * x ^ ε * x ^ (ε / 8) ≤ Y := by
    rw [← hY']; gcongr
  have hnT' := nT_bound hx0 hnT
  have key : 2 * n * m * x ^ ε ≤ 4 * Y * nT := by
    have hme : 0 ≤ m * x ^ ε := by positivity
    have hnT0 : 0 ≤ nT := by nlinarith
    calc 2 * n * m * x ^ ε = 2 * n * (m * x ^ ε) := by ring
      _ ≤ 2 * (2 * nT * x ^ (ε / 8)) * (m * x ^ ε) := by gcongr
      _ = 4 * nT * (m * x ^ ε * x ^ (ε / 8)) := by ring
      _ ≤ 4 * nT * Y := by gcongr
      _ = 4 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc m * ((2 * n) * m * b * x ^ ε) = (2 * n * m * x ^ ε) * (m * b) := by ring
    _ ≤ (4 * Y * nT) * (m * b) := mul_le_mul_of_nonneg_right key hmb
    _ = 4 * Y * (nT * m * b) := by ring

lemma T4 {x ε Y m n nT nT2 b k : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x) (hm0 : 0 ≤ m) (hb : 0 ≤ b) (hε : 0 < ε)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 < n)
    (hnT2 : nT2 ≤ n) (hk0 : 0 ≤ k) (hk2 : k ≤ n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) :
    m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))) ≤ 2 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have pne := Real.rpow_pos_of_pos hx0 (-ε)
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hneg : x ^ (-ε) * x ^ ε = 1 := by rw [← rp hx0]; simp
  have he : m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
      = (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) := by
    have h2 : x ^ ε = 1 / x ^ (-ε) := by rw [eq_div_iff pne.ne', mul_comm, hneg]
    rw [h2]; field_simp
  rw [he]
  have hA : nT2 * k * (x ^ ε * x ^ ε) / n ^ 2 ≤ n * x ^ ((1 : ℝ) / 2 + ε) := by
    rw [div_le_iff₀ (by positivity)]
    have hxe : 0 ≤ x ^ ε * x ^ ε := by positivity
    have e2 : n * x ^ ((1 : ℝ) / 2 + ε) * n ^ 2 = n * (n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) * (x ^ ε * x ^ ε) := by
      rw [show (1 : ℝ) / 2 + ε = ((1 : ℝ) / 2 - ε) + ε + ε by ring, rp hx0, rp hx0]; ring
    rw [e2]
    have := mul_le_mul hnT2 hk2 hk0 hn.le
    exact mul_le_mul_of_nonneg_right this hxe
  have hnT' := nT_bound hx0 hnT
  have hXe : x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8) ≤ Y := by
    rw [← rp hx0, hY]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hB : n * x ^ ((1 : ℝ) / 2 + ε) ≤ 2 * Y * nT := by
    have hp := Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 2 + ε)
    have hnT0 : 0 ≤ nT := by nlinarith
    calc n * x ^ ((1 : ℝ) / 2 + ε) ≤ (2 * nT * x ^ (ε / 8)) * x ^ ((1 : ℝ) / 2 + ε) :=
          mul_le_mul_of_nonneg_right hnT' hp.le
      _ = 2 * nT * (x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8)) := by ring
      _ ≤ 2 * nT * Y := by gcongr
      _ = 2 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) ≤ (m * b) * (n * x ^ ((1 : ℝ) / 2 + ε)) :=
        mul_le_mul_of_nonneg_left hA hmb
    _ ≤ (m * b) * (2 * Y * nT) := mul_le_mul_of_nonneg_left hB hmb
    _ = 2 * Y * (nT * m * b) := by ring

end SZ

theorem growth_unabsorbed (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ)
    (hW : SizeContract C ε x n nT nT2 m b k aE Err)
    (hT : GrowthIneq x ε n nT nT2 m b Err Gx) :
    Gx ≤ 26*x^((1:ℝ)/2+(C+21/8)*ε) := by
  unfold SizeContract SizePremises at hW
  unfold GrowthIneq at hT
  obtain ⟨hW, hErr⟩ := hW
  obtain ⟨hx3, hε, hC, hn, hb, haE0, haE, hnT, hd2, hnT2, hm1, hm2, hk1, hk2⟩ := hW
  unfold bracket at hErr
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have pos : ∀ u : ℝ, 0 < x ^ u := fun u => Real.rpow_pos_of_pos hx0 u
  have mono : ∀ u v : ℝ, u ≤ v → x ^ u ≤ x ^ v := fun u v h => Real.rpow_le_rpow_of_exponent_le hx1 h
  have hP1 : 1 ≤ x ^ (C * ε) := Real.one_le_rpow hx1 (by positivity)
  have hY1 : 1 ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) := Real.one_le_rpow hx1 (by linarith)
  have hXY : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) := mono _ _ (by linarith)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (pos _) hm1
  have hnT0 : (0 : ℝ) < nT := lt_of_lt_of_le (by have := pos (-(ε / 8)); positivity) hnT
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk1
  have hQ : 0 < (nT : ℝ) * m * b := by positivity
  have hxX : x ≤ x ^ ((1 : ℝ) / 2 + ε) * m := by
    have e : x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) = x := by
      rw [← SZ.rp hx0]; norm_num
    calc x = x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) := e.symm
      _ ≤ x ^ ((1 : ℝ) / 2 + ε) * m := mul_le_mul_of_nonneg_left hm1 (pos _).le
  have h1 := SZ.T1 hxX hXY hnT0.le hm0.le hb.le haE
  have h2 := SZ.T2 hx0 hY1 hnT0.le hm0.le hb.le hk0 hk1 haE
  have h3 := SZ.T3 (ε := ε) (n := (n : ℝ)) hx0 hm0.le hb.le rfl hm2 hnT hnR.le
  have h4 := SZ.T4 (nT2 := (nT2 : ℝ)) hx0 hx1 hm0.le hb.le hε rfl hnT hnR (by exact_mod_cast hnT2) hk0.le hk2
  have hErr' : Err ≤ 10 * x ^ (C * ε) * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by
    refine le_trans hErr ?_
    have hsum : (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
        + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
        ≤ 10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by
      have e : (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
          + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
          = (nT : ℝ) * aE + (nT : ℝ) * aE * ((m : ℝ) ^ 2 / k) + (m : ℝ) * ((2 * n) * m * b * x ^ ε)
            + (m : ℝ) * ((nT2 : ℝ) * k * b * x ^ ε / (n * (n * x ^ (-ε)))) := by ring
      rw [e]; linarith
    have hP0 : 0 ≤ x ^ (C * ε) := (pos _).le
    calc x ^ (C * ε) * ((nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
        + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))))
        ≤ x ^ (C * ε) * (10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b)) :=
          mul_le_mul_of_nonneg_left hsum hP0
      _ = 10 * x ^ (C * ε) * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by ring
  generalize hPd : x ^ (C * ε) = P at hErr' hP1
  generalize hYd : x ^ ((1 : ℝ) / 2 + 13 * ε / 8) = Y at hErr' hY1 hXY
  generalize hXd : x ^ ((1 : ℝ) / 2 + ε) = X at hT hXY
  generalize hQd : (nT : ℝ) * m * b = Q at hErr' hQ
  have hT' : Q * ((nT2 : ℝ) / n / 2) * (Gx - 4 * X) ≤ Err + 2 * Q / x := by
    rw [← hQd]; simpa [mul_assoc] using hT
  generalize hδd : ((nT2 : ℝ) / n) = δ at hT' hd2
  have hδ0 : 0 < δ := lt_of_lt_of_le (pos _) hd2
  have hxδ : 1 ≤ x ^ ε * δ := by
    have := mul_le_mul_of_nonneg_left hd2 (pos ε).le
    have e : x ^ ε * x ^ (-ε) = 1 := by rw [← SZ.rp hx0]; simp
    linarith
  have h2x : 2 / x ≤ 1 := by rw [div_le_one hx0]; linarith
  have hPY : 1 ≤ P * Y := by nlinarith
  have hmain : δ * (Gx - 4 * X) ≤ 22 * (P * Y) := by
    have h1 : Q * (δ / 2 * (Gx - 4 * X)) ≤ Q * (10 * P * Y + 2 / x) := by
      have e1 : Q * (δ / 2 * (Gx - 4 * X)) = Q * (δ / 2) * (Gx - 4 * X) := by ring
      have e2 : Q * (10 * P * Y + 2 / x) = 10 * P * Y * Q + 2 * Q / x := by ring
      rw [e1, e2]; linarith
    have h2 := le_of_mul_le_mul_left h1 hQ
    have e3 : δ * (Gx - 4 * X) = 2 * (δ / 2 * (Gx - 4 * X)) := by ring
    have e4 : 10 * P * Y = 10 * (P * Y) := by ring
    rw [e3]; rw [e4] at h2; linarith
  have hG : Gx - 4 * X ≤ 22 * (P * Y) * x ^ ε := by
    by_cases hc : Gx - 4 * X ≤ 0
    · have : 0 ≤ 22 * (P * Y) * x ^ ε := by have := pos ε; positivity
      linarith
    · have hc' : 0 < Gx - 4 * X := lt_of_not_ge hc
      have hxe := pos ε
      calc Gx - 4 * X ≤ (x ^ ε * δ) * (Gx - 4 * X) := le_mul_of_one_le_left hc'.le hxδ
        _ = x ^ ε * (δ * (Gx - 4 * X)) := by ring
        _ ≤ x ^ ε * (22 * (P * Y)) := mul_le_mul_of_nonneg_left hmain hxe.le
        _ = 22 * (P * Y) * x ^ ε := by ring
  have hZ : P * Y * x ^ ε = x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    rw [← hPd, ← hYd, ← SZ.rp hx0, ← SZ.rp hx0]; ring_nf
  have hXZ : X ≤ x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    rw [← hXd]; exact mono _ _ (by have := mul_nonneg hC hε.le; linarith)
  have hG26 : Gx ≤ 26 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    have : 22 * (P * Y) * x ^ ε = 22 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by rw [mul_assoc, hZ]
    linarith
  exact hG26


theorem growth_margin (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err G β : ℝ)
    (hW : SizeContract C ε x n nT nT2 m b k aE Err)
    (hG : GrowthIneq x ε n nT nT2 m b Err G)
    (hβ : 0 < β) (hcap : 26 ≤ x^(β*ε)) :
    G ≤ x^((1:ℝ)/2+(C+21/8+β)*ε) := by
  have hx0 : 0 < x := by linarith [hW.1.1]
  calc
    G ≤ 26*x^((1:ℝ)/2+(C+21/8)*ε) := growth_unabsorbed C ε x n nT nT2 m b k aE Err G hW hG
    _ ≤ x^(β*ε)*x^((1:ℝ)/2+(C+21/8)*ε) :=
      mul_le_mul_of_nonneg_right hcap (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

theorem bracket_nonneg (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ)
    (hW : SizePremises C ε x n nT nT2 m b k aE) :
    0 ≤ bracket x ε n nT nT2 m b k aE := by
  obtain ⟨hx,he,hC,hn,hb,ha,_,_,_,_,hm,_,hk,_⟩ := hW
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < (m:ℝ) := (Real.rpow_pos_of_pos hx0 _).trans_le hm
  have hk0 : 0 < k := (mul_pos hx0 hm0).trans_le hk
  unfold bracket
  positivity

def splitC (eD eL α : ℝ) := max eD (max 2 (1+eL))+α

def SplitInput (eD eL α H ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ) : Prop :=
  SizePremises (splitC eD eL α) ε x n nT nT2 m b k aE ∧
  Err ≤ H*max (x^(eD*ε)) (x^ε*max (x^ε) (x^(eL*ε)))*bracket x ε n nT nT2 m b k aE

theorem split_size (eD eL α H ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ)
    (hd : 0 ≤ eD) (hl : 0 ≤ eL) (hα : 0 < α) (hH : 0 ≤ H)
    (hcap : H ≤ x^(α*ε))
    (hW : SplitInput eD eL α H ε x n nT nT2 m b k aE Err) :
    SizeContract (splitC eD eL α) ε x n nT nT2 m b k aE Err := by
  have hx : 1 ≤ x := by linarith [hW.1.1]
  have he := hW.1.2.1
  have hE := bracket_nonneg _ _ _ _ _ _ _ _ _ _ hW.1
  exact ⟨hW.1, RH26E06F.split_absorb x ε eD eL α H _ Err hx he hd hl hα hH hE hcap hW.2⟩

theorem composed_growth (eD eL α β H ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err G : ℝ)
    (hd : 0 ≤ eD) (hl : 0 ≤ eL) (hα : 0 < α) (hβ : 0 < β)
    (hH : 0 ≤ H) (hcap : H ≤ x^(α*ε)) (h26 : 26 ≤ x^(β*ε))
    (hW : SplitInput eD eL α H ε x n nT nT2 m b k aE Err)
    (hG : GrowthIneq x ε n nT nT2 m b Err G) :
    G ≤ x^((1:ℝ)/2+(splitC eD eL α+21/8+β)*ε) :=
  growth_margin _ _ _ _ _ _ _ _ _ _ _ _ _ (split_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd hl hα hH hcap hW) hG hβ h26

theorem composed_character (eD eL α β γ H ε x o Sig G Gm : ℝ)
    (n nT nT2 m : ℕ) (b k aE Err : ℝ)
    (hd : 0 ≤ eD) (hl : 0 ≤ eL) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hH : 0 ≤ H) (ho : 0 ≤ o)
    (hcap : H ≤ x^(α*ε)) (h26 : 26 ≤ x^(β*ε)) (hchar : 1+4*o ≤ x^(γ*ε))
    (hW : SplitInput eD eL α H ε x n nT nT2 m b k aE Err)
    (hG : GrowthIneq x ε n nT nT2 m b Err G)
    (hSig : Sig ≤ 4*o*x^((1:ℝ)/2+ε)) (hGm : Gm ≤ G+Sig) :
    Gm ≤ x^((1:ℝ)/2+(splitC eD eL α+21/8+β+γ)*ε) := by
  have hcore := composed_growth eD eL α β H ε x n nT nT2 m b k aE Err G hd hl hα hβ hH hcap h26 hW hG
  have hx : 1 ≤ x := by linarith [hW.1.1]
  have hx0 : 0 < x := by linarith
  have he := hW.1.2.1
  let A := (1:ℝ)/2+(splitC eD eL α+21/8+β)*ε
  have hC := hW.1.2.2.1
  have hA : (1:ℝ)/2+ε ≤ A := by
    dsimp [A]
    nlinarith only [mul_nonneg hC he.le,mul_nonneg hβ.le he.le,he]
  have hsmall : x^((1:ℝ)/2+ε) ≤ x^A := Real.rpow_le_rpow_of_exponent_le hx hA
  have hs := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 4*o by positivity)
  change G ≤ x^A at hcore
  calc
    Gm ≤ (1+4*o)*x^A := by linarith only [hGm,hcore,hSig,hs]
    _ ≤ x^(γ*ε)*x^A := mul_le_mul_of_nonneg_right hchar (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; dsimp [A]; ring

def threshold (α β γ H ε o : ℝ) :=
  max 3 (max ((max 1 H)^(1/(α*ε))) (max ((26:ℝ)^(1/(β*ε))) ((1+4*o)^(1/(γ*ε)))))

theorem all_thresholds (α β γ H ε o x : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (he : 0 < ε)
    (hH : 0 ≤ H) (ho : 0 ≤ o) (hx : threshold α β γ H ε o ≤ x) :
    3 ≤ x ∧ H ≤ x^(α*ε) ∧ 26 ≤ x^(β*ε) ∧ 1+4*o ≤ x^(γ*ε) := by
  unfold threshold at hx
  have h3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hrest := (le_max_right _ _).trans hx
  have hA := (le_max_left _ _).trans hrest
  have hrest' := (le_max_right _ _).trans hrest
  have hB := (le_max_left _ _).trans hrest'
  have hC := (le_max_right _ _).trans hrest'
  refine ⟨h3, RH26E06F.explicit_threshold ε α H x he hα hH (max_le (by linarith) hA), ?_, ?_⟩
  · apply RH26E06F.explicit_threshold ε β 26 x he hβ (by norm_num)
    rw [max_eq_right (by norm_num : (1:ℝ) ≤ 26)]
    exact max_le (by linarith) hB
  · apply RH26E06F.explicit_threshold ε γ (1+4*o) x he hγ (by positivity)
    rw [max_eq_right (by linarith : (1:ℝ) ≤ 1+4*o)]
    exact max_le (by linarith) hC

theorem split_bracket_transport (Q d P x X Y Z t1 t2 t3 t4 Err G : ℝ)
    (hQ : 0 < Q) (hd : 0 < d) (hP : 0 ≤ P) (hx : 0 < x)
    (h1 : t1 ≤ 2*X*Q) (h2 : t2 ≤ 2*Q) (h3 : t3 ≤ 4*Y*Q) (h4 : t4 ≤ 2*d*Z*Q)
    (hE : Err ≤ P*(t1+t2+t3+t4))
    (hG : Q*(d/2)*(G-4*X) ≤ Err+2*Q/x) :
    G ≤ 4*X+(4*P*X+4*P+8*P*Y+4/x)/d+4*P*Z := by
  have hsum : t1+t2+t3+t4 ≤ Q*(2*X+2+4*Y+2*d*Z) := by linarith only [h1,h2,h3,h4]
  have hmul := mul_le_mul_of_nonneg_left hsum hP
  have h0 : Q*(d/2*(G-4*X)) ≤ Q*(P*(2*X+2+4*Y+2*d*Z)+2/x) := by
    calc
      Q*(d/2*(G-4*X)) = Q*(d/2)*(G-4*X) := by ring
      _ ≤ Err+2*Q/x := hG
      _ ≤ P*(t1+t2+t3+t4)+2*Q/x := by linarith only [hE]
      _ ≤ P*(Q*(2*X+2+4*Y+2*d*Z))+2*Q/x := by linarith only [hmul]
      _ = Q*(P*(2*X+2+4*Y+2*d*Z)+2/x) := by ring
  have h := le_of_mul_le_mul_left h0 hQ
  have hdG : d*(G-4*X-4*P*Z) ≤ 4*P*X+4*P+8*P*Y+4/x := by linarith only [h]
  have hfin := (le_div_iff₀ hd).2 hdG
  linarith only [hfin]

theorem source_parameter_controls :
    splitC 2 0 1+21/8+3/8+1 = 7 ∧
    splitC 2 0 (1/8)+21/8+1/8+1/8 = 5 ∧
    (2:ℝ)+0+7=9 := by norm_num [splitC,max_def]

theorem strict_margin_control (ε β : ℝ) (he : 0 < ε) (hβ : 0 < β) :
    ¬ ((26:ℝ) ≤ (1:ℝ)^(β*ε)) := by norm_num

end
end RH26E06G

#print axioms RH26E06G.growth_unabsorbed
#print axioms RH26E06G.growth_margin
#print axioms RH26E06G.bracket_nonneg
#print axioms RH26E06G.split_size
#print axioms RH26E06G.composed_growth
#print axioms RH26E06G.composed_character
#print axioms RH26E06G.all_thresholds
#print axioms RH26E06G.split_bracket_transport
#print axioms RH26E06G.source_parameter_controls
#print axioms RH26E06G.strict_margin_control
