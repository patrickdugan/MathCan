import Mathlib

/- Independent Mathlib candidate. Run with the pinned GRH Mathlib project.
   This file proves only abstract scalar arithmetic and a divisibility lemma. -/
namespace MathCan.GRHC

theorem exact_comparison (d n H R L I : ℝ)
    (h : d * (H - 3 * L) ≤ n * (H - R + L) + 2 * d * I) :
    n * R ≤ d * (4 * L + 2 * I) - (d - n) * (H + L) := by
  ring_nf at h ⊢
  linarith only [h]

theorem relaxed_comparison (d n H R L I : ℝ)
    (hn : n ≤ d) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (h : d * (H - 3 * L) ≤ n * (H - R + L) + 2 * d * I) :
    n * R ≤ d * (4 * L + 2 * I) := by
  have h₁ := exact_comparison d n H R L I h
  have h₂ : 0 ≤ (d - n) * (H + L) :=
    mul_nonneg (sub_nonneg.mpr hn) (add_nonneg hH hL)
  linarith only [h₁, h₂]

theorem coverage_comparison (d n H R L I ρ : ℝ)
    (hd : 0 < d) (hn : n ≤ d) (hρ : 0 < ρ)
    (hcover : ρ * d ≤ n) (hH : 0 ≤ H) (hL : 0 ≤ L) (hI : 0 ≤ I)
    (h : d * (H - 3 * L) ≤ n * (H - R + L) + 2 * d * I) :
    ρ * R ≤ 4 * L + 2 * I := by
  by_cases hR : R ≤ 0
  · have hzero : ρ * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ.le hR
    linarith only [hzero, hL, hI]
  · have h₁ := relaxed_comparison d n H R L I hn hH hL h
    have h₂ := mul_le_mul_of_nonneg_right hcover (le_of_lt (lt_of_not_ge hR))
    have h₃ : d * (ρ * R) ≤ d * (4 * L + 2 * I) := calc
      d * (ρ * R) = (ρ * d) * R := by ring
      _ ≤ n * R := h₂
      _ ≤ d * (4 * L + 2 * I) := h₁
    exact le_of_mul_le_mul_left h₃ hd

theorem scalar_lift (p a b : ℤ) (g h : ℕ)
    (ha : p ^ g ∣ a) (hb : p ^ h ∣ b) : p ^ (g + h) ∣ a * b := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x * y, ?_⟩
  rw [hx, hy, pow_add]
  ring

#print axioms exact_comparison
#print axioms relaxed_comparison
#print axioms coverage_comparison
#print axioms scalar_lift
end MathCan.GRHC
