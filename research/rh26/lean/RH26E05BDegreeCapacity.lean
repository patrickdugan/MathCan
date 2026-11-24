import Mathlib

/-!
Independent finite local-rank and degree-normalized capacity certificate.
The arithmetic realization of the nested index sets, rank and degree
premises is external (RH26B08/B10/B11).
-/

namespace RH26E05B

open scoped BigOperators

noncomputable def mass {P : Type*} (J : Finset P) (m : P → ℝ) : ℝ :=
  ∑ p ∈ J, m p

noncomputable def dualBound {I : Type*} (A : Finset I) (d E : I → ℝ)
    (R lam : ℝ) : ℝ :=
  lam * R + ∑ i ∈ A, d i * max (E i - lam) 0

theorem local_mass_bound {P : Type*} (J : Finset P) (m q : P → ℝ)
    (eta E : ℝ) (hm : ∀ p ∈ J, 0 ≤ m p)
    (hq : ∀ p ∈ J, q p ≤ E)
    (heta : eta ≤ ∑ p ∈ J, m p * q p) :
    eta ≤ E * mass J m := by
  calc
    _ ≤ ∑ p ∈ J, m p * q p := heta
    _ ≤ ∑ p ∈ J, E * m p := by
      apply Finset.sum_le_sum
      intro p hp
      rw [mul_comm E (m p)]
      exact mul_le_mul_of_nonneg_left (hq p hp) (hm p hp)
    _ = _ := by rw [mass, Finset.mul_sum]

theorem finite_dual_bound {I : Type*} (A : Finset I) (m d E : I → ℝ)
    (R lam : ℝ) (hm : ∀ i ∈ A, 0 ≤ m i)
    (hd : ∀ i ∈ A, m i ≤ d i) (hR : (∑ i ∈ A, m i) ≤ R)
    (hlam : 0 ≤ lam) :
    (∑ i ∈ A, m i * E i) ≤ dualBound A d E R lam := by
  have hc : ∀ i ∈ A, m i * E i ≤
      lam * m i + d i * max (E i - lam) 0 := by
    intro i hi
    by_cases h : E i ≤ lam
    · rw [max_eq_right (sub_nonpos.mpr h), mul_zero, add_zero]
      calc
        _ ≤ m i * lam := mul_le_mul_of_nonneg_left h (hm i hi)
        _ = _ := mul_comm _ _
    · have hp : 0 ≤ E i - lam := sub_nonneg.mpr (le_of_not_ge h)
      rw [max_eq_left hp]
      have hh := mul_le_mul_of_nonneg_right (hd i hi) hp
      linarith only [hh]
  have hs := Finset.sum_le_sum hc
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hb := mul_le_mul_of_nonneg_left hR hlam
  unfold dualBound
  linarith only [hs, hb]

theorem place_capacity {I P : Type*} (A : Finset I) (J : I → Finset P)
    (m q : I → P → ℝ) (eta d E : I → ℝ) (R lam : ℝ)
    (hm : ∀ i ∈ A, ∀ p ∈ J i, 0 ≤ m i p)
    (hq : ∀ i ∈ A, ∀ p ∈ J i, q i p ≤ E i)
    (heta : ∀ i ∈ A, eta i ≤ ∑ p ∈ J i, m i p * q i p)
    (hd : ∀ i ∈ A, mass (J i) (m i) ≤ d i)
    (hR : (∑ i ∈ A, mass (J i) (m i)) ≤ R)
    (hlam : 0 ≤ lam) :
    (∑ i ∈ A, eta i) ≤ dualBound A d E R lam := by
  have hmass : ∀ i ∈ A, 0 ≤ mass (J i) (m i) := by
    intro i hi
    unfold mass
    exact Finset.sum_nonneg (hm i hi)
  calc
    _ ≤ ∑ i ∈ A, mass (J i) (m i) * E i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_comm]
      exact local_mass_bound (J i) (m i) (q i) (eta i) (E i)
        (hm i hi) (hq i hi) (heta i hi)
    _ ≤ _ := finite_dual_bound A (fun i => mass (J i) (m i)) d E R lam
      hmass hd hR hlam

theorem uniform_place_bound {I P : Type*} (A : Finset I) (J : I → Finset P)
    (m q : I → P → ℝ) (eta E : I → ℝ) (R U : ℝ)
    (hm : ∀ i ∈ A, ∀ p ∈ J i, 0 ≤ m i p)
    (hq : ∀ i ∈ A, ∀ p ∈ J i, q i p ≤ E i)
    (heta : ∀ i ∈ A, eta i ≤ ∑ p ∈ J i, m i p * q i p)
    (hE : ∀ i ∈ A, E i ≤ U) (hU : 0 ≤ U)
    (hR : (∑ i ∈ A, mass (J i) (m i)) ≤ R) :
    (∑ i ∈ A, eta i) ≤ R * U := by
  calc
    _ ≤ ∑ i ∈ A, U * mass (J i) (m i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact local_mass_bound (J i) (m i) (q i) (eta i) U
        (hm i hi) (fun p hp => (hq i hi p hp).trans (hE i hi)) (heta i hi)
    _ = U * ∑ i ∈ A, mass (J i) (m i) := by rw [Finset.mul_sum]
    _ ≤ U * R := mul_le_mul_of_nonneg_left hR hU
    _ = R * U := mul_comm _ _

noncomputable def coverage {W : Type*} (S : Finset W) (z : W → ℝ) (D : ℝ) : ℝ :=
  (∑ w ∈ S, z w) / D

noncomputable def weight {W : Type*} (L D : ℝ) (z : W → ℝ) (w : W) : ℝ :=
  L * (z w / D)

theorem degree_coverage {W : Type*} (S : Finset W) (z : W → ℝ) (D : ℝ)
    (hD : 0 < D) (hz : ∀ w ∈ S, 0 ≤ z w)
    (hs : (∑ w ∈ S, z w) ≤ D) :
    0 ≤ coverage S z D ∧ coverage S z D ≤ 1 := by
  unfold coverage
  exact ⟨div_nonneg (Finset.sum_nonneg hz) hD.le,
    (div_le_iff₀ hD).2 (by simpa using hs)⟩

theorem weight_normalization {W : Type*} (S : Finset W) (z : W → ℝ) (L D : ℝ) :
    (∑ w ∈ S, weight L D z w) = L * coverage S z D := by
  simp only [weight, coverage, Finset.sum_div, Finset.mul_sum]

theorem coverage_slack_identity {W : Type*} (S : Finset W)
    (z Bp : W → ℝ) (L D B : ℝ) :
    (∑ w ∈ S, weight L D z w * min B (Bp w)) =
      L * B - L * (1 - coverage S z D) * B -
        ∑ w ∈ S, weight L D z w * max (B - Bp w) 0 := by
  have hm : ∀ w, min B (Bp w) = B - max (B - Bp w) 0 := by
    intro w
    rcases le_total B (Bp w) with h | h
    · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), sub_zero]
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
      ring
  calc
    _ = ∑ w ∈ S, (weight L D z w * B -
          weight L D z w * max (B - Bp w) 0) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [hm w]
      ring
    _ = (∑ w ∈ S, weight L D z w) * B -
          ∑ w ∈ S, weight L D z w * max (B - Bp w) 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = _ := by rw [weight_normalization]; ring

theorem degree_weighted_bound {W : Type*} (S : Finset W)
    (z eta Bp : W → ℝ) (L D B : ℝ)
    (hL : 0 ≤ L) (hD : 0 < D) (hz : ∀ w ∈ S, 0 ≤ z w)
    (hs : (∑ w ∈ S, z w) ≤ D) (hB : 0 ≤ B)
    (hu : ∀ w ∈ S, eta w ≤ B) (hc : ∀ w ∈ S, eta w ≤ Bp w) :
    (∑ w ∈ S, weight L D z w * eta w) ≤
      L * B - L * (1 - coverage S z D) * B -
        ∑ w ∈ S, weight L D z w * max (B - Bp w) 0 ∧
    0 ≤ L * (1 - coverage S z D) * B ∧
    0 ≤ ∑ w ∈ S, weight L D z w * max (B - Bp w) 0 := by
  have hw : ∀ w ∈ S, 0 ≤ weight L D z w :=
    fun w hw => mul_nonneg hL (div_nonneg (hz w hw) hD.le)
  have ha := degree_coverage S z D hD hz hs
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ ∑ w ∈ S, weight L D z w * min B (Bp w) :=
        Finset.sum_le_sum (fun w hw' =>
          mul_le_mul_of_nonneg_left (le_min (hu w hw') (hc w hw')) (hw w hw'))
      _ = _ := coverage_slack_identity S z Bp L D B
  · exact mul_nonneg (mul_nonneg hL (sub_nonneg.mpr ha.2)) hB
  · exact Finset.sum_nonneg (fun w hw' =>
      mul_nonneg (hw w hw') (le_max_right _ _))

theorem nested_export {W I P : Type*} (S : Finset W)
    (A : W → Finset I) (J : W → I → Finset P)
    (m q : W → I → P → ℝ) (eta d E : W → I → ℝ)
    (z lam : W → ℝ) (L D R U : ℝ)
    (hL : 0 ≤ L) (hD : 0 < D) (hz : ∀ w ∈ S, 0 ≤ z w)
    (hs : (∑ w ∈ S, z w) ≤ D) (hR : 0 ≤ R) (hU : 0 ≤ U)
    (hm : ∀ w ∈ S, ∀ i ∈ A w, ∀ p ∈ J w i, 0 ≤ m w i p)
    (hq : ∀ w ∈ S, ∀ i ∈ A w, ∀ p ∈ J w i, q w i p ≤ E w i)
    (heta : ∀ w ∈ S, ∀ i ∈ A w, eta w i ≤ ∑ p ∈ J w i, m w i p * q w i p)
    (hd : ∀ w ∈ S, ∀ i ∈ A w, mass (J w i) (m w i) ≤ d w i)
    (hbudget : ∀ w ∈ S, (∑ i ∈ A w, mass (J w i) (m w i)) ≤ R)
    (hE : ∀ w ∈ S, ∀ i ∈ A w, E w i ≤ U)
    (hlam : ∀ w ∈ S, 0 ≤ lam w) :
    (∑ w ∈ S, weight L D z w * (∑ i ∈ A w, eta w i)) ≤
      L * (R * U) - L * (1 - coverage S z D) * (R * U) -
        (∑ w ∈ S, weight L D z w *
          max (R * U - dualBound (A w) (d w) (E w) R (lam w)) 0) ∧
    0 ≤ L * (1 - coverage S z D) * (R * U) ∧
    0 ≤ ∑ w ∈ S, weight L D z w *
      max (R * U - dualBound (A w) (d w) (E w) R (lam w)) 0 := by
  exact degree_weighted_bound S z (fun w => ∑ i ∈ A w, eta w i)
    (fun w => dualBound (A w) (d w) (E w) R (lam w))
    L D (R * U) hL hD hz hs (mul_nonneg hR hU)
    (fun w hw => uniform_place_bound (A w) (J w) (m w) (q w) (eta w) (E w) R U
      (hm w hw) (hq w hw) (heta w hw) (hE w hw) hU (hbudget w hw))
    (fun w hw => place_capacity (A w) (J w) (m w) (q w) (eta w) (d w) (E w) R (lam w)
      (hm w hw) (hq w hw) (heta w hw) (hd w hw) (hbudget w hw) (hlam w hw))

noncomputable def fixtureD (i : Fin 2) : ℝ := if i = 0 then 1 else 3
noncomputable def fixtureE (i : Fin 2) : ℝ := if i = 0 then 9 else 2
noncomputable def missingM (i : Fin 2) : ℝ := if i = 0 then 2 else 0

theorem exact_fixture :
    (∀ i : Fin 2, (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ fixtureD i) ∧
    (∑ _i : Fin 2, (1 : ℝ)) ≤ 2 ∧
    (∑ i : Fin 2, (1 : ℝ) * fixtureE i) = 11 ∧
    dualBound (Finset.univ : Finset (Fin 2)) fixtureD fixtureE 2 2 = 11 ∧
    coverage (Finset.univ : Finset Unit) (fun _ => 2) 4 = 1/2 ∧
    (∑ w : Unit, weight 1 4 (fun _ => 2) w * (∑ i : Fin 2, (1 : ℝ) * fixtureE i)) = 11/2 ∧
    (1 : ℝ) * (2 * 9) = 18 ∧
    1 * (1 - coverage (Finset.univ : Finset Unit) (fun _ => 2) 4) * 18 = 9 ∧
    (∑ w : Unit, weight 1 4 (fun _ => 2) w *
      max (18 - dualBound (Finset.univ : Finset (Fin 2)) fixtureD fixtureE 2 2) 0) = 7/2 ∧
    (18 : ℝ) - 9 - 7/2 = 11/2 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [fixtureD]
  · norm_num [fixtureE, fixtureD, dualBound, weight, coverage, Fin.sum_univ_two, max_def]

theorem missing_cap_control :
    (∀ i : Fin 2, 0 ≤ missingM i) ∧
    (∑ i : Fin 2, missingM i) ≤ 2 ∧
    fixtureD 0 < missingM 0 ∧
    (∑ i : Fin 2, missingM i * fixtureE i) = 18 ∧
    dualBound (Finset.univ : Finset (Fin 2)) fixtureD fixtureE 2 2 = 11 ∧
    dualBound (Finset.univ : Finset (Fin 2)) fixtureD fixtureE 2 2 <
      ∑ i : Fin 2, missingM i * fixtureE i := by
  constructor
  · intro i
    fin_cases i <;> norm_num [missingM]
  · norm_num [missingM, fixtureD, fixtureE, dualBound, Fin.sum_univ_two, max_def]

theorem excess_coverage_control :
    (0 : ℝ) < 1 ∧ (∀ _w : Unit, (0 : ℝ) ≤ 2) ∧
    1 < coverage (Finset.univ : Finset Unit) (fun _ => 2) 1 ∧
    (∑ w : Unit, weight 1 1 (fun _ => 2) w * (1 : ℝ)) = 2 ∧
    (1 : ℝ) * 1 < 2 ∧
    1 * (1 - coverage (Finset.univ : Finset Unit) (fun _ => 2) 1) * 1 < 0 := by
  norm_num [weight, coverage]

end RH26E05B

#print axioms RH26E05B.local_mass_bound
#print axioms RH26E05B.finite_dual_bound
#print axioms RH26E05B.place_capacity
#print axioms RH26E05B.uniform_place_bound
#print axioms RH26E05B.degree_coverage
#print axioms RH26E05B.weight_normalization
#print axioms RH26E05B.coverage_slack_identity
#print axioms RH26E05B.degree_weighted_bound
#print axioms RH26E05B.nested_export
#print axioms RH26E05B.exact_fixture
#print axioms RH26E05B.missing_cap_control
#print axioms RH26E05B.excess_coverage_control
