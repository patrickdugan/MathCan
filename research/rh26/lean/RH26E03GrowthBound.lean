import Mathlib

/-!
Independent scalar proof motivated by RH26C02_ERROR_BRACKET and
RH26C03_NORMALIZATION. All analytical and family-realization premises remain
external. Natural source cardinalities embed in the real-valued window below.
-/

namespace RH26E03

def bracket (x eps n N P m b k a : ℝ) : ℝ :=
  N * a * (1 + m ^ 2 / k) +
    m * ((2 * n) * m * b * x ^ eps +
      P * k * b * x ^ eps / (n * (n * x ^ (-eps))))

def perSlot (x eps n N P m b k a : ℝ) : ℝ :=
  a / (m * b) + a * m / (b * k) +
    (2 * n / N) * m * x ^ eps +
    (P / N) * (k / n ^ 2) * x ^ (2 * eps)

structure Window (x eps n N P m b k a : ℝ) : Prop where
  x_min : 3 ≤ x
  eps_pos : 0 < eps
  n_pos : 0 < n
  b_pos : 0 < b
  a_nonneg : 0 ≤ a
  a_upper : a ≤ 2 * x * b
  N_lower : x ^ (-(eps / 8)) * n / 2 ≤ N
  density_lower : x ^ (-eps) ≤ P / n
  P_upper : P ≤ n
  m_lower : x ^ ((1 : ℝ) / 2 - eps) ≤ m
  m_upper : m ≤ x ^ ((1 : ℝ) / 2 + eps / 2)
  k_lower : x * m ≤ k
  k_upper : k ≤ n ^ 2 * x ^ ((1 : ℝ) / 2 - eps)
  absorb : 26 ≤ x ^ (3 * eps / 8)

private theorem pow_join {x : ℝ} (hx : 0 < x) (u v : ℝ) :
    x ^ u * x ^ v = x ^ (u + v) :=
  (Real.rpow_add hx u v).symm

private theorem opposite_powers {x : ℝ} (hx : 0 < x) (u : ℝ) :
    x ^ (-u) * x ^ u = 1 := by
  rw [pow_join hx]
  simp

theorem window_positive {x eps n N P m b k a : ℝ}
    (h : Window x eps n N P m b k a) :
    0 < x ∧ 0 < N ∧ 0 < P ∧ 0 < m ∧ 0 < k := by
  have hx : 0 < x := by linarith [h.x_min]
  have hp8 := Real.rpow_pos_of_pos hx (-(eps / 8))
  have hN := lt_of_lt_of_le
    (div_pos (mul_pos hp8 h.n_pos) (by norm_num : (0 : ℝ) < 2)) h.N_lower
  have hdelta := lt_of_lt_of_le (Real.rpow_pos_of_pos hx (-eps)) h.density_lower
  have hP : 0 < P := by
    have hh := (lt_div_iff₀ h.n_pos).1 hdelta
    simpa using hh
  have hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hx ((1 : ℝ) / 2 - eps)) h.m_lower
  exact ⟨hx, hN, hP, hm, lt_of_lt_of_le (mul_pos hx hm) h.k_lower⟩

theorem bracket_normalization (x eps n N P m b k a : ℝ)
    (hx : 0 < x) (hn : 0 < n) (hN : 0 < N)
    (hm : 0 < m) (hb : 0 < b) (hk : 0 < k) :
    bracket x eps n N P m b k a / (N * m * b) = perSlot x eps n N P m b k a := by
  have he := Real.rpow_pos_of_pos hx eps
  have hneg : x ^ (-eps) = 1 / x ^ eps :=
    (eq_div_iff he.ne').2 (opposite_powers hx eps)
  have htwo : x ^ (2 * eps) = x ^ eps * x ^ eps := by
    rw [pow_join hx]
    congr 1
    ring
  unfold bracket perSlot
  rw [hneg, htwo]
  field_simp [hn.ne', hN.ne', hm.ne', hb.ne', hk.ne', he.ne'] <;> ring

theorem card_ratio {x eps n N P m b k a : ℝ}
    (h : Window x eps n N P m b k a) :
    n / N ≤ 2 * x ^ (eps / 8) := by
  obtain ⟨hx, hN, _, _, _⟩ := window_positive h
  have hp := Real.rpow_pos_of_pos hx (eps / 8)
  have hh := mul_le_mul_of_nonneg_right h.N_lower hp.le
  have heq : (x ^ (-(eps / 8)) * n / 2) * x ^ (eps / 8) = n / 2 := by
    calc
      _ = (x ^ (-(eps / 8)) * x ^ (eps / 8)) * (n / 2) := by ring
      _ = _ := by rw [opposite_powers hx, one_mul]
  rw [heq] at hh
  apply (div_le_iff₀ hN).2
  nlinarith only [hh]

theorem component_bounds {x eps n N P m b k a : ℝ}
    (h : Window x eps n N P m b k a) :
    a / (m * b) ≤ 2 * x / m ∧
    a * m / (b * k) ≤ 2 ∧
    (2 * n / N) * m * x ^ eps ≤ 4 * m * x ^ (9 * eps / 8) ∧
    (P / N) * (k / n ^ 2) * x ^ (2 * eps) ≤ 2 * x ^ ((1 : ℝ) / 2 + 9 * eps / 8) := by
  obtain ⟨hx, hN, hP, hm, hk⟩ := window_positive h
  have hb := h.b_pos
  have hn := h.n_pos
  have he := Real.rpow_pos_of_pos hx eps
  have hp8 := Real.rpow_pos_of_pos hx (eps / 8)
  have hr := card_ratio h
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      a / (m * b) ≤ (2 * x * b) / (m * b) :=
        div_le_div_of_nonneg_right h.a_upper (mul_nonneg hm.le hb.le)
      _ = 2 * x / m := by field_simp [hm.ne', hb.ne'] <;> ring
  · apply (div_le_iff₀ (mul_pos hb hk)).2
    have ha := mul_le_mul_of_nonneg_right h.a_upper hm.le
    have hkk := mul_le_mul_of_nonneg_left h.k_lower (show 0 ≤ 2 * b by positivity)
    nlinarith only [ha, hkk]
  · have hr2 : 2 * n / N ≤ 4 * x ^ (eps / 8) := by
      calc
        _ = 2 * (n / N) := by ring
        _ ≤ 2 * (2 * x ^ (eps / 8)) := mul_le_mul_of_nonneg_left hr (by norm_num)
        _ = _ := by ring
    calc
      _ ≤ (4 * x ^ (eps / 8)) * m * x ^ eps :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr2 hm.le) he.le
      _ = (4 * m) * (x ^ (eps / 8) * x ^ eps) := by ring
      _ = _ := by rw [pow_join hx, show eps / 8 + eps = 9 * eps / 8 by ring]
  · have hpN : P / N ≤ 2 * x ^ (eps / 8) :=
      (div_le_div_of_nonneg_right h.P_upper hN.le).trans hr
    have hkn : k / n ^ 2 ≤ x ^ ((1 : ℝ) / 2 - eps) := by
      apply (div_le_iff₀ (show 0 < n ^ 2 by positivity)).2
      simpa only [mul_comm] using h.k_upper
    have hmul := mul_le_mul hpN hkn (div_nonneg hk.le (sq_nonneg n))
      (show 0 ≤ 2 * x ^ (eps / 8) by positivity)
    calc
      _ ≤ (2 * x ^ (eps / 8) * x ^ ((1 : ℝ) / 2 - eps)) * x ^ (2 * eps) :=
        mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg hx.le _)
      _ = 2 * ((x ^ (eps / 8) * x ^ ((1 : ℝ) / 2 - eps)) * x ^ (2 * eps)) := by ring
      _ = _ := by
        rw [pow_join hx, pow_join hx,
          show eps / 8 + ((1 : ℝ) / 2 - eps) + 2 * eps = (1 : ℝ) / 2 + 9 * eps / 8 by ring]

private theorem inverse_m_bound {x eps n N P m b k a : ℝ}
    (h : Window x eps n N P m b k a) :
    x / m ≤ x ^ ((1 : ℝ) / 2 + eps) := by
  obtain ⟨hx, _, _, hm, _⟩ := window_positive h
  apply (div_le_iff₀ hm).2
  calc
    x = x ^ (((1 : ℝ) / 2 - eps) + ((1 : ℝ) / 2 + eps)) := by
      rw [show (1 : ℝ) / 2 - eps + (1 / 2 + eps) = 1 by ring, Real.rpow_one]
    _ = x ^ ((1 : ℝ) / 2 - eps) * x ^ ((1 : ℝ) / 2 + eps) := (pow_join hx _ _).symm
    _ ≤ m * x ^ ((1 : ℝ) / 2 + eps) :=
      mul_le_mul_of_nonneg_right h.m_lower (Real.rpow_nonneg hx.le _)
    _ = _ := mul_comm _ _

theorem bracket_bound {x eps n N P m b k a : ℝ}
    (h : Window x eps n N P m b k a) :
    bracket x eps n N P m b k a / (N * m * b) ≤
      10 * x ^ ((1 : ℝ) / 2 + 13 * eps / 8) := by
  obtain ⟨hx, hN, _, hm, hk⟩ := window_positive h
  have hx1 : 1 ≤ x := by linarith [h.x_min]
  let Y := x ^ ((1 : ℝ) / 2 + 13 * eps / 8)
  have hY1 : 1 ≤ Y := Real.one_le_rpow hx1 (by linarith [h.eps_pos])
  have hxy : x / m ≤ Y := (inverse_m_bound h).trans
    (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [h.eps_pos]))
  have hmY : m * x ^ (9 * eps / 8) ≤ Y := by
    calc
      _ ≤ x ^ ((1 : ℝ) / 2 + eps / 2) * x ^ (9 * eps / 8) :=
        mul_le_mul_of_nonneg_right h.m_upper (Real.rpow_nonneg hx.le _)
      _ = Y := by
        dsimp [Y]
        rw [pow_join hx, show (1 : ℝ) / 2 + eps / 2 + 9 * eps / 8 =
          (1 : ℝ) / 2 + 13 * eps / 8 by ring]
  have h4Y : x ^ ((1 : ℝ) / 2 + 9 * eps / 8) ≤ Y :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [h.eps_pos])
  obtain ⟨h1, h2, h3, h4⟩ := component_bounds h
  rw [bracket_normalization x eps n N P m b k a hx h.n_pos hN hm h.b_pos hk]
  unfold perSlot
  change _ ≤ 10 * Y
  linarith only [h1, h2, h3, h4, hY1, hxy, hmY, h4Y]

theorem two_term_envelope {x eps n N P m b k a : ℝ}
    (h : Window x eps n N P m b k a) (hm1 : 1 ≤ m) :
    bracket x eps n N P m b k a / (N * m * b) ≤
      x ^ (13 * eps / 8) * (4 * x / m + 6 * m) := by
  obtain ⟨hx, hN, _, hm, hk⟩ := window_positive h
  have hx1 : 1 ≤ x := by linarith [h.x_min]
  let L := x ^ (13 * eps / 8)
  have hL1 : 1 ≤ L := Real.one_le_rpow hx1 (by linarith [h.eps_pos])
  have hLm : 1 ≤ L * m := by
    calc
      1 ≤ L := hL1
      _ ≤ L * m := le_mul_of_one_le_right (by linarith) hm1
  have ha : 2 * x / m ≤ 2 * (x / m * L) := by
    have hh := le_mul_of_one_le_right (div_nonneg hx.le hm.le) hL1
    linarith only [hh]
  have hc : m * x ^ (9 * eps / 8) ≤ m * L :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [h.eps_pos])) hm.le
  have hd : x ^ ((1 : ℝ) / 2 + 9 * eps / 8) ≤ x / m * L := by
    have hh := mul_le_mul_of_nonneg_right h.m_upper
      (Real.rpow_nonneg hx.le ((1 : ℝ) / 2 + 9 * eps / 8))
    have heq : x ^ ((1 : ℝ) / 2 + eps / 2) * x ^ ((1 : ℝ) / 2 + 9 * eps / 8) = x * L := by
      calc
        _ = x ^ (1 + 13 * eps / 8) := by
          rw [pow_join hx, show (1 : ℝ) / 2 + eps / 2 + ((1 : ℝ) / 2 + 9 * eps / 8) =
            1 + 13 * eps / 8 by ring]
        _ = x ^ (1 : ℝ) * x ^ (13 * eps / 8) := (pow_join hx _ _).symm
        _ = x * L := by rw [Real.rpow_one]; rfl
    rw [heq] at hh
    have hh' : x ^ ((1 : ℝ) / 2 + 9 * eps / 8) * m ≤ x * L := by
      simpa only [mul_comm] using hh
    have hd' : x ^ ((1 : ℝ) / 2 + 9 * eps / 8) ≤ (x * L) / m :=
      (le_div_iff₀ hm).2 hh'
    calc
      _ ≤ (x * L) / m := hd'
      _ = _ := by ring
  obtain ⟨h1, h2, h3, h4⟩ := component_bounds h
  rw [bracket_normalization x eps n N P m b k a hx h.n_pos hN hm h.b_pos hk]
  unfold perSlot
  change _ ≤ L * (4 * x / m + 6 * m)
  linarith only [h1, h2, h3, h4, hLm, ha, hc, hd]

theorem density_inverse {x eps delta : ℝ} (hx : 0 < x)
    (hdelta : x ^ (-eps) ≤ delta) : 1 / delta ≤ x ^ eps := by
  have hp := Real.rpow_pos_of_pos hx eps
  have hd := lt_of_lt_of_le (Real.rpow_pos_of_pos hx (-eps)) hdelta
  have hh := mul_le_mul_of_nonneg_right hdelta hp.le
  rw [opposite_powers hx] at hh
  apply (div_le_iff₀ hd).2
  simpa only [mul_comm] using hh

theorem density_normalize (Q delta x H B J G : ℝ)
    (hQ : 0 < Q) (hd : 0 < delta) (hx : 0 < x)
    (h : Q * (delta / 2) * (G - 4 * J) ≤ H * B + 2 * Q / x) :
    G ≤ (2 / delta) * H * (B / Q) + 4 / (delta * x) + 4 * J := by
  have hp : 0 < Q * (delta / 2) := by positivity
  have hh : G - 4 * J ≤ (H * B + 2 * Q / x) / (Q * (delta / 2)) := by
    apply (le_div_iff₀ hp).2
    simpa only [mul_comm (G - 4 * J)] using h
  have heq : (H * B + 2 * Q / x) / (Q * (delta / 2)) =
      (2 / delta) * H * (B / Q) + 4 / (delta * x) := by
    field_simp [hQ.ne', hd.ne', hx.ne'] <;> ring
  rw [heq] at hh
  linarith only [hh]

theorem growth_bound {x eps n N P m b k a C Err G : ℝ}
    (h : Window x eps n N P m b k a) (hC : 0 ≤ C)
    (hErr : Err ≤ x ^ (C * eps) * bracket x eps n N P m b k a)
    (hInput : N * m * b * ((P / n) / 2) *
        (G - 4 * x ^ ((1 : ℝ) / 2 + eps)) ≤ Err + 2 * (N * m * b) / x) :
    G ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * eps) := by
  obtain ⟨hx, hN, hP, hm, _⟩ := window_positive h
  have hx1 : 1 ≤ x := by linarith [h.x_min]
  let Q := N * m * b
  let delta := P / n
  let H := x ^ (C * eps)
  let B := bracket x eps n N P m b k a
  let Y := x ^ ((1 : ℝ) / 2 + 13 * eps / 8)
  let Z := x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * eps)
  let J := x ^ ((1 : ℝ) / 2 + eps)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hd : 0 < delta := div_pos hP h.n_pos
  have hH : 0 < H := Real.rpow_pos_of_pos hx _
  have hY : 0 < Y := Real.rpow_pos_of_pos hx _
  have hZ : 0 < Z := Real.rpow_pos_of_pos hx _
  have hR : B / Q ≤ 10 * Y := bracket_bound h
  have hInv : 1 / delta ≤ x ^ eps := density_inverse hx h.density_lower
  have hInv2 : 2 / delta ≤ 2 * x ^ eps := by
    calc
      _ = 2 * (1 / delta) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by norm_num)
  have hInput' : Q * (delta / 2) * (G - 4 * J) ≤ H * B + 2 * Q / x :=
    hInput.trans (add_le_add_right hErr _)
  have hNorm := density_normalize Q delta x H B J G hQ hd hx hInput'
  have hFirst : (2 / delta) * H * (B / Q) ≤ 20 * Z := by
    calc
      _ ≤ (2 / delta) * H * (10 * Y) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ ≤ (2 * x ^ eps) * H * (10 * Y) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hInv2 hH.le) (by positivity)
      _ = 20 * Z := by
        dsimp [H, Y, Z]
        calc
          _ = 20 * ((x ^ eps * x ^ (C * eps)) * x ^ ((1 : ℝ) / 2 + 13 * eps / 8)) := by ring
          _ = _ := by
            rw [pow_join hx, pow_join hx,
              show eps + C * eps + ((1 : ℝ) / 2 + 13 * eps / 8) =
                (1 : ℝ) / 2 + (C + 21 / 8) * eps by ring]
  have hCE : 0 ≤ C * eps := mul_nonneg hC h.eps_pos.le
  have hJZ : J ≤ Z := Real.rpow_le_rpow_of_exponent_le hx1 (by
    nlinarith only [hCE, h.eps_pos])
  have heZ : x ^ eps ≤ Z := Real.rpow_le_rpow_of_exponent_le hx1 (by
    nlinarith only [hCE, h.eps_pos])
  have h4x : 4 / x ≤ 2 := (div_le_iff₀ hx).2 (by linarith [h.x_min])
  have hRem : 4 / (delta * x) ≤ 2 * Z := by
    calc
      _ = (1 / delta) * (4 / x) := by ring
      _ ≤ x ^ eps * (4 / x) := mul_le_mul_of_nonneg_right hInv (by positivity)
      _ ≤ Z * 2 := mul_le_mul heZ h4x (by positivity) hZ.le
      _ = _ := by ring
  have hSum : G ≤ 26 * Z := by linarith only [hNorm, hFirst, hRem, hJZ]
  calc
    G ≤ 26 * Z := hSum
    _ ≤ x ^ (3 * eps / 8) * Z := mul_le_mul_of_nonneg_right h.absorb hZ.le
    _ = _ := by
      dsimp [Z]
      rw [pow_join hx, show 3 * eps / 8 + ((1 : ℝ) / 2 + (C + 21 / 8) * eps) =
        (1 : ℝ) / 2 + (C + 3) * eps by ring]

theorem zero_density_control :
    ∃ G : ℝ, (1 : ℝ) * (0 / 2) * (G - 4 * 1) ≤ 1 * 0 + 2 * 1 / 1 ∧ 26 < G := by
  exact ⟨27, by norm_num⟩

theorem zero_volume_control :
    ∃ G : ℝ, (0 : ℝ) * (1 / 2) * (G - 4 * 1) ≤ 1 * 0 + 2 * 0 / 1 ∧ 26 < G := by
  exact ⟨27, by norm_num⟩

theorem missing_density_control :
    ∃ (Q delta x H B J G : ℝ), 0 < Q ∧ 0 < delta ∧ delta ≤ 1 ∧ 0 < x ∧
      Q * (delta / 2) * (G - 4 * J) ≤ H * B + 2 * Q / x ∧
      2 * H * (B / Q) + 4 / x + 4 * J < G := by
  exact ⟨1, 1 / 8, 4, 1, 1, 1, 28, by norm_num⟩

/-- Actual natural cardinality/slot values; no realization of the host data claimed. -/
theorem no_loss_family (t : ℕ) (A D : ℝ) (ht : 2 ≤ t)
    (hA : 0 < A) (hD : 0 < D)
    (hAbs : 26 ≤ ((t : ℝ) ^ 2) ^ ((3 : ℝ) / 8))
    (hBig : A + D < 2 * (t : ℝ) ^ 2) :
    let z : ℝ := t
    let x := z ^ 2
    Window x 1 x x x z z (x * z) (x * z) ∧
      A * x / z + D * z <
        bracket x 1 x x x z z (x * z) (x * z) / (x * z * z) := by
  let z : ℝ := t
  let x := z ^ 2
  change Window x 1 x x x z z (x * z) (x * z) ∧
    A * x / z + D * z < bracket x 1 x x x z z (x * z) (x * z) / (x * z * z)
  have hz2 : 2 ≤ z := by exact_mod_cast ht
  have hz : 0 < z := by linarith
  have hx3 : 3 ≤ x := by
    dsimp [x]
    nlinarith only [hz2, sq_nonneg (z - 2)]
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hroot : x ^ ((1 : ℝ) / 2) = z := by
    rw [← Real.sqrt_eq_rpow]
    dsimp [x]
    exact Real.sqrt_sq hz.le
  have hpow8 : x ^ (-((1 : ℝ) / 8)) ≤ 1 := by
    calc
      _ ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = 1 := by simp
  have hpow1 : x ^ (-(1 : ℝ)) ≤ 1 := by
    calc
      _ ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = 1 := by simp
  have hcancel : x ^ ((1 : ℝ) / 2 - 1) * z = 1 := by
    rw [← hroot, pow_join hx]
    norm_num
  have hkeq : x ^ 2 * x ^ ((1 : ℝ) / 2 - 1) = x * z := by
    apply mul_right_cancel₀ hz.ne'
    calc
      _ = x ^ 2 * (x ^ ((1 : ℝ) / 2 - 1) * z) := by ring
      _ = x ^ 2 := by rw [hcancel, mul_one]
      _ = _ := by dsimp [x]; ring
  have hwin : Window x 1 x x x z z (x * z) (x * z) := by
    constructor
    · exact hx3
    · norm_num
    · exact hx
    · exact hz
    · positivity
    · nlinarith only [mul_pos hx hz]
    · calc
        _ ≤ 1 * x / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow8 hx.le) (by norm_num)
        _ ≤ _ := by linarith
    · rw [div_self hx.ne']
      exact hpow1
    · exact le_rfl
    · rw [← hroot]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    · rw [← hroot]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    · exact le_rfl
    · exact le_of_eq hkeq.symm
    · simpa only [mul_one, x, z] using hAbs
  refine ⟨hwin, ?_⟩
  have hEq3 : (2 * x / x) * z * x ^ (1 : ℝ) = 2 * z * x := by
    rw [Real.rpow_one]
    field_simp [hx.ne'] <;> ring
  have hLower : 2 * z * x ≤ perSlot x 1 x x x z z (x * z) (x * z) := by
    unfold perSlot
    rw [hEq3]
    have h1 : 0 ≤ (x * z) / (z * z) := by positivity
    have h2 : 0 ≤ (x * z) * z / (z * (x * z)) := by positivity
    have h4 : 0 ≤ (x / x) * ((x * z) / x ^ 2) * x ^ (2 * (1 : ℝ)) := by positivity
    linarith only [h1, h2, h4]
  have hdiv : x / z = z := by dsimp [x]; field_simp [hz.ne'] <;> ring
  have hleft : A * x / z + D * z = (A + D) * z := by
    calc
      _ = A * (x / z) + D * z := by ring
      _ = _ := by rw [hdiv]; ring
  rw [hleft, bracket_normalization x 1 x x x z z (x * z) (x * z) hx hx hx hz hz (mul_pos hx hz)]
  have hBig' : A + D < 2 * x := hBig
  have hlt := mul_lt_mul_of_pos_right hBig' hz
  exact lt_of_lt_of_le (by nlinarith only [hlt]) hLower

theorem no_uniform_no_loss (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ t : ℕ, 2 ≤ t ∧
      (let z : ℝ := t
       let x := z ^ 2
       Window x 1 x x x z z (x * z) (x * z) ∧
         A * x / z + D * z <
           bracket x 1 x x x z z (x * z) (x * z) / (x * z * z)) := by
  obtain ⟨u, hu⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (show 0 < (3 : ℝ) / 8 by norm_num)).eventually_ge_atTop 26)
  obtain ⟨t, ht⟩ := exists_nat_gt (max 2 (max u (A + D + 1)))
  have ht2r : (2 : ℝ) ≤ (t : ℝ) := (le_max_left _ _).trans ht.le
  have ht2 : 2 ≤ t := by exact_mod_cast ht2r
  have htu : u ≤ (t : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans ht.le)
  have hta : A + D + 1 ≤ (t : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht.le)
  have hsq : (t : ℝ) ≤ (t : ℝ) ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  exact ⟨t, ht2, no_loss_family t A D ht2 hA hD (hu _ (htu.trans hsq))
    (by linarith only [hta, hsq, ht2r])⟩

end RH26E03

#print axioms RH26E03.window_positive
#print axioms RH26E03.bracket_normalization
#print axioms RH26E03.card_ratio
#print axioms RH26E03.component_bounds
#print axioms RH26E03.bracket_bound
#print axioms RH26E03.two_term_envelope
#print axioms RH26E03.density_inverse
#print axioms RH26E03.density_normalize
#print axioms RH26E03.growth_bound
#print axioms RH26E03.zero_density_control
#print axioms RH26E03.zero_volume_control
#print axioms RH26E03.missing_density_control
#print axioms RH26E03.no_loss_family
#print axioms RH26E03.no_uniform_no_loss
