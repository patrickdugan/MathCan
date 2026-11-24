import ObserverBound

/-! Finite algebra for QBTC-05. No asymptotic oracle security, independence,
Chernoff or AC0 claim is encoded by these lemmas. -/
open scoped BigOperators
namespace CRYPTVP
noncomputable section

theorem weighted_cost_le {A : Type*} [Fintype A]
    (p q g : A → ℝ) (c : ℝ)
    (h : ∀ a, q a ≤ c * p a) (hg : ∀ a, 0 ≤ g a) :
    (∑ a, q a * g a) ≤ c * ∑ a, p a * g a := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  calc
    q a * g a ≤ (c * p a) * g a := mul_le_mul_of_nonneg_right (h a) (hg a)
    _ = c * (p a * g a) := by ring

theorem empirical_mixture_le {A B : Type*} [Fintype A]
    (p q : A → ℝ) (D : A → B → ℝ) (c : ℝ)
    (h : ∀ a, q a ≤ c * p a) (hD : ∀ a b, 0 ≤ D a b) (b : B) :
    (∑ a, q a * D a b) ≤ c * ∑ a, p a * D a b :=
  weighted_cost_le p q (fun a => D a b) c h (fun a => hD a b)

theorem list_weight_nonneg {A : Type*} (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (xs : List A) :
    0 ≤ (xs.map p).prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_nonneg (hp a) ih

/-- Product domination for independent replacement draws conditional on the source table. -/
theorem product_weight_le {A : Type*} (p q : A → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (h : ∀ a, q a ≤ c * p a) (xs : List A) :
    (xs.map q).prod ≤ c ^ xs.length * (xs.map p).prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    calc
      q a * (xs.map q).prod ≤
          (c * p a) * (c ^ xs.length * (xs.map p).prod) :=
        mul_le_mul (h a) ih (list_weight_nonneg q hq xs) (mul_nonneg hc (hp a))
      _ = (c ^ xs.length * c) * (p a * (xs.map p).prod) := by ring

/-- Exceptional contexts pay their probability mass times a cost bound. -/
theorem bad_mass_bound {A : Type*} [Fintype A] (good : A → Prop)
    [DecidablePred good] (w ind copy : A → ℝ) (c B : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hci : ∀ a, 0 ≤ c * ind a)
    (hg : ∀ a, good a → copy a ≤ c * ind a)
    (hb : ∀ a, ¬ good a → copy a ≤ B) :
    (∑ a, w a * copy a) ≤ c * (∑ a, w a * ind a) +
      B * (∑ a, if good a then 0 else w a) := by
  classical
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  by_cases h : good a
  · simp only [if_pos h, mul_zero, add_zero]
    calc
      w a * copy a ≤ w a * (c * ind a) :=
        mul_le_mul_of_nonneg_left (hg a h) (hw a)
      _ = c * (w a * ind a) := by ring
  · simp only [if_neg h]
    calc
      w a * copy a ≤ w a * B := mul_le_mul_of_nonneg_left (hb a h) (hw a)
      _ ≤ w a * B + w a * (c * ind a) :=
        le_add_of_nonneg_right (mul_nonneg (hw a) (hci a))
      _ = c * (w a * ind a) + B * w a := by ring

/-- Algebraic size-bias cancellation. c is the number of witnesses;
    q is selector success conditional on the table, and vanishes if c=0. -/
theorem planted_recovery_sum {A : Type*} [Fintype A]
    (w c q : A → ℝ) (mu : ℝ) (hm : mu ≠ 0)
    (hz : ∀ a, c a = 0 → q a = 0) :
    (∑ a, (w a * c a / mu) * (q a / c a)) =
      (∑ a, w a * q a) / mu := by
  classical
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hc : c a = 0
  · simp [hc, hz a hc]
  · field_simp [hc, hm] <;> ring

end
end CRYPTVP

#print axioms CRYPTVP.weighted_cost_le
#print axioms CRYPTVP.empirical_mixture_le
#print axioms CRYPTVP.list_weight_nonneg
#print axioms CRYPTVP.product_weight_le
#print axioms CRYPTVP.bad_mass_bound
#print axioms CRYPTVP.planted_recovery_sum
