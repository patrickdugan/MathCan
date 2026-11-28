import Mathlib

/-! Direct strengthened scalar adaptation of upstream core_ineq,
leanprover-community/riemann-hypothesis at c900e67c2fcd1fdb041685820bbd2b867fbc5a4b,
SubThreeMulLogTwoLe.lean:62–256. Original hypotheses and LHS retained;
only the sufficient hbig premise removed, and the envelope split.
Conditional scalar certificate, not an arithmetic family realization. -/
namespace RH26E06F
noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 1500000

def coeff (K h g : ℝ) : ℝ := 5*K^2+16*K+2+8*h*(5*K^2+13*K+2*K*g+2)

theorem core_ineq_split {nT a b b' k L La B0 Nc M sA lW lk lH dI et Xpp y yD yL K h g
    cDiv cE cH cCount cSlope cSl1 cLoss : ℝ}
    (hy : 1 ≤ y) (hyD : 1 ≤ yD) (hyL : 1 ≤ yL)
    (hnT : 1 ≤ nT) (ha1 : 1 ≤ a) (hb0 : 0 ≤ b) (hba : b ≤ a) (hM : 0 ≤ M) (hk : 0 < k) (hMk : M ≤ k)
    (hMb : M * b ≤ a) (hL0 : 0 ≤ L) (hL : L ≤ 2 * y) (hLa0 : 0 ≤ La) (hLa : La ≤ 2 * y)
    (hb' : 0 ≤ b') (hkb' : k * b' ≤ a) (hX0 : 0 ≤ Xpp) (hX : Xpp ≤ a)
    (hsA0 : 0 ≤ sA) (hsA : sA ≤ 2 * (nT * a)) (hB0 : 0 ≤ B0) (hNc : 0 ≤ Nc)
    (hlW : lW ≤ a) (hlk0 : 0 ≤ lk) (hlk : lk ≤ g * y) (hlH0 : 0 ≤ lH) (hlH : lH ≤ h * y)
    (hdI0 : 0 ≤ dI) (hdI : dI ≤ 2) (het : et ≤ K * y * (nT * a))
    (c1 : 0 ≤ cDiv) (c1' : cDiv ≤ K) (c2 : 0 ≤ cE) (c2' : cE ≤ K) (c3 : 0 ≤ cH) (c3' : cH ≤ K)
    (c4 : 0 ≤ cCount) (c4' : cCount ≤ K) (c5 : 0 ≤ cSlope) (c5' : cSlope ≤ K)
    (c6 : 0 ≤ cSl1) (c6' : cSl1 ≤ K) (c7 : 0 ≤ cLoss) (c7' : cLoss ≤ K)
    (hh : 1 ≤ h) (hg : 1 ≤ g) :
    sA * (cCount * (La + M ^ 2 * La / k))
      + (cDiv * nT * a * La + cDiv * M * (B0 + Nc) * yD)
      + M * cE * B0
      + cSlope * nT * a * La * (1 + M / k)
      + lW
      + cLoss * nT * M * b * yL
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1)
      + dI * (4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) + et)
      ≤ coeff K h g * max yD (y * max y yL) * (nT * a * (1 + M ^ 2 / k) + M * (B0 + Nc)) := by
  have hK : 0 ≤ K := c1.trans c1'
  have hy0 : 0 ≤ y := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hnT0 : 0 ≤ nT := by linarith
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨r, hr⟩ : ∃ r, r = M ^ 2 / k := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = M / k := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by rw [hq]; exact (div_le_one hk).2 hMk
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = nT * a := ⟨_, rfl⟩
  have hA1a : a ≤ A1 := by rw [hA1]; exact le_mul_of_one_le_left ha0 hnT
  have hA10 : 0 ≤ A1 := by linarith
  obtain ⟨A3, hA3⟩ : ∃ A3, A3 = M * B0 := ⟨_, rfl⟩
  have hA30 : 0 ≤ A3 := by rw [hA3]; positivity
  obtain ⟨A4, hA4⟩ : ∃ A4, A4 = M * Nc := ⟨_, rfl⟩
  have hA40 : 0 ≤ A4 := by rw [hA4]; positivity
  obtain ⟨E, hE⟩ : ∃ E, E = A1 * (1 + r) + (A3 + A4) := ⟨_, rfl⟩
  have hA1r : 0 ≤ A1 * r := mul_nonneg hA10 hr0
  have orbitMap_conj_smul_one : A1 ≤ E := by rw [hE]; linarith only [hA1r, hA30, hA40]
  have eA1r : A1 * (1 + r) ≤ E := by rw [hE]; linarith only [hA30, hA40]
  have orbitMap_conj_smul_two : A1 * r ≤ E := by rw [hE]; linarith only [hA10, hA30, hA40]
  have selfLieBasisVector : A3 ≤ E := by rw [hE]; linarith only [hA10, hA1r, hA40]
  have eA34 : A3 + A4 ≤ E := by rw [hE]; linarith only [hA10, hA1r]
  have hE0 : 0 ≤ E := hA10.trans orbitMap_conj_smul_one
  have e1 : 1 ≤ E := by linarith only [ha1, hA1a, orbitMap_conj_smul_one]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = max y yL := ⟨_, rfl⟩
  have yY : y ≤ Y := by rw [hY]; exact le_max_left _ _
  have oneY : 1 ≤ Y := hy.trans yY
  have yLY : yL ≤ Y := by rw [hY]; exact le_max_right _ _
  have hY0 : 0 ≤ Y := by linarith
  obtain ⟨P, hP⟩ : ∃ P, P = Y * E := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have EP : E ≤ P := by rw [hP]; exact le_mul_of_one_le_left hE0 oneY
  have hLaY : La ≤ 2 * Y := by linarith only [hLa, yY]
  have hLY : L ≤ 2 * Y := by linarith only [hL, yY]
  have hlkY : lk ≤ g * Y := hlk.trans (by gcongr)

  have T1 : sA * (cCount * (La + M ^ 2 * La / k)) ≤ 4 * K * P := by
    have e : sA * (cCount * (La + M ^ 2 * La / k)) = (sA * (1 + r)) * (cCount * La) := by
      rw [hr]; ring
    have s1 : sA * (1 + r) ≤ 2 * E := by
      have : sA * (1 + r) ≤ 2 * A1 * (1 + r) := by rw [hA1]; gcongr
      linarith only [this, eA1r]
    rw [e]
    calc (sA * (1 + r)) * (cCount * La) ≤ (2 * E) * (K * (2 * Y)) := by gcongr
      _ = 4 * K * P := by rw [hP]; ring
  have T2a : cDiv * nT * a * La ≤ 2 * K * P := by
    calc cDiv * nT * a * La = cDiv * A1 * La := by rw [hA1]; ring
      _ ≤ K * E * (2 * Y) := by gcongr
      _ = 2 * K * P := by rw [hP]; ring
  have T2b : cDiv * M * (B0 + Nc) * yD ≤ K * yD * E := by
    calc cDiv * M * (B0 + Nc) * yD = cDiv * (A3 + A4) * yD := by rw [hA3, hA4]; ring
      _ ≤ K * E * yD := by gcongr
      _ = K * yD * E := by ring
  have T3 : M * cE * B0 ≤ K * P := by
    calc M * cE * B0 = cE * A3 := by rw [hA3]; ring
      _ ≤ K * P := by gcongr; exact selfLieBasisVector.trans EP
  have T4 : cSlope * nT * a * La * (1 + M / k) ≤ 4 * K * P := by
    calc cSlope * nT * a * La * (1 + M / k) = cSlope * A1 * La * (1 + q) := by rw [hA1, hq]; ring
      _ ≤ K * E * (2 * Y) * (1 + 1) := by gcongr
      _ = 4 * K * P := by rw [hP]; ring
  have T5 : lW ≤ P := by linarith only [hlW, hA1a, orbitMap_conj_smul_one, EP]
  have T60 : 0 ≤ cLoss * nT * M * b * yL := by positivity
  have FreeQuotientRank : cLoss * nT * M * b * yL ≤ K * P := by
    calc cLoss * nT * M * b * yL = cLoss * (nT * (M * b)) * yL := by ring
      _ ≤ K * (nT * a) * Y := by gcongr
      _ ≤ K * E * Y := by rw [← hA1]; gcongr
      _ = K * P := by rw [hP]; ring
  have Tmid : cSl1 * nT * M * (a / k + b') * (cCount * M * L) ≤ 4 * K ^ 2 * P := by
    have hb'k : b' ≤ a / k := by rw [le_div_iff₀ hk]; linarith
    have hQ : nT * M ^ 2 * (a / k + b') ≤ 2 * E := by
      calc nT * M ^ 2 * (a / k + b') ≤ nT * M ^ 2 * (a / k + a / k) := by gcongr
        _ = 2 * (A1 * r) := by rw [hA1, hr]; ring
        _ ≤ 2 * E := by linarith
    have hQ0 : 0 ≤ nT * M ^ 2 * (a / k + b') := by positivity
    calc cSl1 * nT * M * (a / k + b') * (cCount * M * L)
        = cSl1 * cCount * L * (nT * M ^ 2 * (a / k + b')) := by ring
      _ ≤ K * K * (2 * Y) * (2 * E) := by gcongr
      _ = 4 * K ^ 2 * P := by rw [hP]; ring
  have T7 : cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
      + cSl1 * Xpp + 1 ≤ (5 * K ^ 2 + K + 1) * P := by
    have s1 : cSl1 * (cLoss * nT * M * b * yL) ≤ K * (K * P) := by gcongr
    have s2 : cSl1 * Xpp ≤ K * P := by gcongr; linarith only [hX, hA1a, orbitMap_conj_smul_one, EP]
    have s3 : 1 ≤ P := e1.trans EP
    linarith only [s1, s2, s3, Tmid]
  have TU : cSlope * nT * a * La * (2 + M / k)
      + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
      + cSl1 * M * B0
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1) + b ≤ (5 * K ^ 2 + 13 * K + 2 * K * g + 2) * P := by
    have s1 : cSlope * nT * a * La * (2 + M / k) ≤ 6 * K * P := by
      calc cSlope * nT * a * La * (2 + M / k) = cSlope * A1 * La * (2 + q) := by rw [hA1, hq]; ring
        _ ≤ K * E * (2 * Y) * (2 + 1) := by gcongr
        _ = 6 * K * P := by rw [hP]; ring
    have s2 : cH * (nT * a * La + M * B0) ≤ 3 * K * P := by
      calc cH * (nT * a * La + M * B0) = cH * (A1 * La + A3) := by rw [hA1, hA3]
        _ ≤ K * (E * (2 * Y) + P) := by gcongr; exact selfLieBasisVector.trans EP
        _ = 3 * K * P := by rw [hP]; ring
    have s3 : sA * (cCount * lk) ≤ 2 * K * g * P := by
      calc sA * (cCount * lk) ≤ (2 * E) * (K * (g * Y)) := by
            gcongr
            rw [← hA1] at hsA; linarith
        _ = 2 * K * g * P := by rw [hP]; ring
    have s4 : cSl1 * M * B0 ≤ K * P := by
      calc cSl1 * M * B0 = cSl1 * A3 := by rw [hA3]; ring
        _ ≤ K * P := by gcongr; exact selfLieBasisVector.trans EP
    have s5 : b ≤ P := by linarith only [hba, hA1a, orbitMap_conj_smul_one, EP]
    linarith only [s1, s2, s3, s4, s5, T3, T7]
  have Tet : et ≤ K * P := by
    calc et ≤ K * y * A1 := by rw [hA1]; exact het
      _ ≤ K * Y * E := by gcongr
      _ = K * P := by rw [hP]; ring
  obtain ⟨u, hu⟩ : ∃ u, u = 5 * K ^ 2 + 13 * K + 2 * K * g + 2 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  rw [← hu] at TU
  have T8 : dI * (4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) + et) ≤ 2 * (4 * (h * y) * (u * P) + K * P) := by
    have s1 : 4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) ≤ 4 * (h * y) * (u * P) := by
      calc _ ≤ 4 * lH * (u * P) := by gcongr
        _ ≤ 4 * (h * y) * (u * P) := by gcongr
    have s2 : 0 ≤ 4 * (h * y) * (u * P) + K * P := by positivity
    calc _ ≤ dI * (4 * (h * y) * (u * P) + K * P) := by gcongr
      _ ≤ 2 * (4 * (h * y) * (u * P) + K * P) := by gcongr

  let V : ℝ := max yD (y * Y)
  have hyYV : y * Y ≤ V := le_max_right _ _
  have hyDV : yD ≤ V := le_max_left _ _
  have hYP : y * P ≤ V * E := by
    rw [hP, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hyYV hE0
  have hPV : P ≤ V * E :=
    (le_mul_of_one_le_left hP0 hy).trans hYP
  have hDE : yD * E ≤ V * E := mul_le_mul_of_nonneg_right hyDV hE0
  have b1 := mul_le_mul_of_nonneg_left hPV (show 0 ≤ 5*K^2+15*K+2 by positivity)
  have b2 := mul_le_mul_of_nonneg_left hYP (show 0 ≤ 8*h*u by positivity)
  have b3 := mul_le_mul_of_nonneg_left hDE hK
  have hfin : (5*K^2+13*K+2)*P + K*yD*E +
      2*(4*(h*y)*(u*P)+K*P) ≤ coeff K h g * (V*E) := by
    unfold coeff
    rw [← hu]
    linarith only [b1,b2,b3]
  have hR : coeff K h g * max yD (y*max y yL) *
      (nT*a*(1+M^2/k)+M*(B0+Nc)) = coeff K h g * (V*E) := by
    dsimp [V]
    rw [hY,hE,hA1,hA3,hA4,hr]
    ring
  rw [hR]
  linarith only [T1,T2a,T2b,T3,T4,T5,FreeQuotientRank,T7,T8,hfin]


theorem h_poly_bound (K h g : ℝ) (hK : 0 ≤ K) (hh : 1 ≤ h) (hg : 1 ≤ g) :
    coeff K h g ≤ (45*K^2+136*K+18)*h*g := by
  have hhg : 1 ≤ h*g := one_le_mul_of_one_le_of_one_le hh hg
  have a1 : 5*K^2+16*K+2 ≤ (5*K^2+16*K+2)*(h*g) :=
    le_mul_of_one_le_right (by positivity) hhg
  have a2 : 5*K^2+13*K+2*K*g+2 ≤ (5*K^2+15*K+2)*g := by
    nlinarith only [mul_nonneg (show 0 ≤ 5*K^2+13*K+2 by positivity) (show 0 ≤ g-1 by linarith)]
  have a3 := mul_le_mul_of_nonneg_left a2 (show 0 ≤ 8*h by positivity)
  unfold coeff
  linarith only [a1,a3]

theorem h_53 (K h g : ℝ) (hK : 0 ≤ K) (hh : 1 ≤ h) (hg : 1 ≤ g) :
    coeff K h g ≤ 53*(1+K)^2*h*g := by
  have hp : 45*K^2+136*K+18 ≤ 53*(1+K)^2 := by
    nlinarith only [sq_nonneg (K-15/8)]
  calc
    _ ≤ (45*K^2+136*K+18)*h*g := h_poly_bound K h g hK hh hg
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by linarith)) (by linarith)

theorem h_52_control :
    52*(1+(50/23:ℝ))^2 < coeff (50/23) 1 1 := by
  norm_num [coeff]

theorem split_power (x eps eD eL : ℝ) (hx : 1 ≤ x) (he : 0 < eps)
    (hd : 0 ≤ eD) (hl : 0 ≤ eL) :
    max (x^(eD*eps)) (x^eps * max (x^eps) (x^(eL*eps))) =
      x^(max eD (max 2 (1+eL))*eps) := by
  have hx0 : 0 < x := by linarith
  have mx (a b : ℝ) : max (x^a) (x^b) = x^(max a b) := by
    by_cases hab : a ≤ b
    · rw [max_eq_right (Real.rpow_le_rpow_of_exponent_le hx hab), max_eq_right hab]
    · have hba : b ≤ a := le_of_not_ge hab
      rw [max_eq_left (Real.rpow_le_rpow_of_exponent_le hx hba), max_eq_left hba]
  have hinner : eps+max eps (eL*eps) = max 2 (1+eL)*eps := by
    by_cases h : eL ≤ 1
    · rw [max_eq_left (show eL*eps ≤ eps by nlinarith [mul_nonneg (show 0 ≤ 1-eL by linarith) he.le]),
          max_eq_left (show 1+eL ≤ 2 by linarith)]
      ring
    · have h' : 1 ≤ eL := le_of_lt (lt_of_not_ge h)
      rw [max_eq_right (show eps ≤ eL*eps by nlinarith [mul_nonneg (show 0 ≤ eL-1 by linarith) he.le]),
          max_eq_right (show 2 ≤ 1+eL by linarith)]
      ring
  rw [mx eps (eL*eps), ← Real.rpow_add hx0, hinner, mx (eD*eps) (max 2 (1+eL)*eps)]
  have hm : max (eD*eps) (max 2 (1+eL)*eps) = max eD (max 2 (1+eL))*eps := by
    by_cases h : eD ≤ max 2 (1+eL)
    · rw [max_eq_right (mul_le_mul_of_nonneg_right h he.le),max_eq_right h]
    · have h' := le_of_not_ge h
      rw [max_eq_left (mul_le_mul_of_nonneg_right h' he.le),max_eq_left h']
  rw [hm]

theorem split_absorb (x eps eD eL delta H E Err : ℝ)
    (hx : 1 ≤ x) (he : 0 < eps) (hd : 0 ≤ eD) (hl : 0 ≤ eL)
    (hδ : 0 < delta) (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hcap : H ≤ x^(delta*eps))
    (herr : Err ≤ H * max (x^(eD*eps)) (x^eps * max (x^eps) (x^(eL*eps))) * E) :
    Err ≤ x^((max eD (max 2 (1+eL))+delta)*eps)*E := by
  have hx0 : 0 < x := by linarith
  rw [split_power x eps eD eL hx he hd hl] at herr
  calc
    Err ≤ H * x^(max eD (max 2 (1+eL))*eps) * E := herr
    _ ≤ x^(delta*eps) * x^(max eD (max 2 (1+eL))*eps) * E := by gcongr
    _ = _ := by rw [← Real.rpow_add hx0]; congr 2 <;> ring

theorem original_parameters :
    max (2:ℝ) (max 2 (1+0)) = 2 ∧ (2:ℝ)+0+3 = 5 ∧
    max (2:ℝ) (max 2 (1+0))+1 = 3 := by
  norm_num [max_def]

theorem explicit_threshold (eps delta H x : ℝ) (he : 0 < eps)
    (hδ : 0 < delta) (hH : 0 ≤ H)
    (hx : max 1 ((max 1 H)^(1/(delta*eps))) ≤ x) :
    H ≤ x^(delta*eps) := by
  have hp : 0 < delta*eps := mul_pos hδ he
  have hb : 0 ≤ max 1 H := le_trans zero_le_one (le_max_left _ _)
  have hh : (max 1 H)^(1/(delta*eps)) ≤ x := (le_max_right _ _).trans hx
  have hpw := Real.rpow_le_rpow (Real.rpow_nonneg hb _) hh hp.le
  rw [← Real.rpow_mul hb, show 1/(delta*eps)*(delta*eps)=1 by field_simp [hp.ne'], Real.rpow_one] at hpw
  exact (le_max_right _ _).trans hpw

theorem final_character_absorb (x eps eD eL delta o G : ℝ)
    (hx : 1 ≤ x) (he : 0 < eps) (hδ : 0 < delta)
    (hd : 0 ≤ eD) (hl : 0 ≤ eL) (ho : 0 ≤ o)
    (hG : G ≤ x^(1/2+(eD+eL+6)*eps)+4*o*x^(1/2+eps))
    (hcap : 1+4*o ≤ x^(delta*eps)) :
    G ≤ x^(1/2+(eD+eL+6+delta)*eps) := by
  have hx0 : 0 < x := by linarith
  let A := 1/2+(eD+eL+6)*eps
  have hsmall : x^(1/2+eps) ≤ x^A := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    dsimp [A]
    nlinarith [mul_nonneg hd he.le,mul_nonneg hl he.le]
  have hscale : 4*o*x^(1/2+eps) ≤ 4*o*x^A := mul_le_mul_of_nonneg_left hsmall (by positivity)
  calc
    G ≤ (1+4*o)*x^A := by change G ≤ _; dsimp [A] at hscale ⊢; linarith only [hG,hscale]
    _ ≤ x^(delta*eps)*x^A := mul_le_mul_of_nonneg_right hcap (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; dsimp [A]; ring

theorem split_controls :
    max ((2:ℝ)^2) (2*max 2 (2^0)) = 4 ∧
    (2:ℝ)^2*2^0*2^3 = 32 ∧ (2:ℝ)^3=8 := by
  norm_num [max_def]

end
end RH26E06F

#print axioms RH26E06F.core_ineq_split
#print axioms RH26E06F.h_poly_bound
#print axioms RH26E06F.h_53
#print axioms RH26E06F.h_52_control
#print axioms RH26E06F.split_power
#print axioms RH26E06F.split_absorb
#print axioms RH26E06F.original_parameters
#print axioms RH26E06F.explicit_threshold
#print axioms RH26E06F.final_character_absorb
#print axioms RH26E06F.split_controls
