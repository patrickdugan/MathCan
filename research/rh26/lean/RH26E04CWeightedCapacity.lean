import Mathlib

/-!
Independent capped allocation certificates motivated by the local rank
budget in RH26B08. The arithmetic objective and its realization remain
outside this module.
-/

namespace RH26E04C

open scoped BigOperators

noncomputable def pospart (t : ℝ) : ℝ := max t 0
noncomputable def negpart (t : ℝ) : ℝ := max (-t) 0

noncomputable def primal {I : Type*} [Fintype I] (m e : I → ℝ) : ℝ :=
  ∑ i, m i * e i

noncomputable def dual {I : Type*} [Fintype I] (u e : I → ℝ)
    (R lam : ℝ) : ℝ :=
  lam * R + ∑ i, u i * pospart (e i - lam)

noncomputable def coordSlack (m u e lam : ℝ) : ℝ :=
  (u - m) * pospart (e - lam) + m * negpart (e - lam)

def Feasible {I : Type*} [Fintype I] (m u : I → ℝ) (R : ℝ) : Prop :=
  (∀ i, 0 ≤ m i) ∧ (∀ i, m i ≤ u i) ∧ (∑ i, m i) ≤ R

def Complementary {I : Type*} [Fintype I] (m u e : I → ℝ)
    (R lam : ℝ) : Prop :=
  lam * (R - ∑ i, m i) = 0 ∧
    ∀ i, (u i - m i) * pospart (e i - lam) = 0 ∧
      m i * negpart (e i - lam) = 0

private theorem pospart_nonneg (t : ℝ) : 0 ≤ pospart t :=
  le_max_right _ _

private theorem negpart_nonneg (t : ℝ) : 0 ≤ negpart t :=
  le_max_right _ _

theorem hinge_split (t : ℝ) : t = pospart t - negpart t := by
  unfold pospart negpart
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), sub_zero]
  · rw [max_eq_right ht, max_eq_left (neg_nonneg.mpr ht)] <;> ring

theorem coordinate_gap (m u e lam : ℝ) :
    u * pospart (e - lam) + lam * m - m * e = coordSlack m u e lam := by
  have h : m * (e - lam) =
      m * (pospart (e - lam) - negpart (e - lam)) :=
    congrArg (fun z : ℝ => m * z) (hinge_split (e - lam))
  unfold coordSlack
  linear_combination -h

section Finite

variable {I : Type*} [Fintype I]

theorem dual_gap_identity (m u e : I → ℝ) (R lam : ℝ) :
    dual u e R lam - primal m e =
      lam * (R - ∑ i, m i) + ∑ i, coordSlack (m i) (u i) (e i) lam := by
  classical
  have hsum :
      (∑ i, u i * pospart (e i - lam) + lam * m i - m i * e i) =
        ∑ i, coordSlack (m i) (u i) (e i) lam := by
    apply Finset.sum_congr rfl
    intro i _
    exact coordinate_gap (m i) (u i) (e i) lam
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  unfold dual primal
  linear_combination hsum

private theorem coordinate_slack_nonneg (m u e lam : ℝ)
    (hm : 0 ≤ m) (hu : m ≤ u) : 0 ≤ coordSlack m u e lam :=
  add_nonneg
    (mul_nonneg (sub_nonneg.mpr hu) (pospart_nonneg _))
    (mul_nonneg hm (negpart_nonneg _))

theorem dual_bound (m u e : I → ℝ) (R lam : ℝ)
    (hf : Feasible m u R) (hlam : 0 ≤ lam) :
    primal m e ≤ dual u e R lam := by
  have hbudget : 0 ≤ lam * (R - ∑ i, m i) :=
    mul_nonneg hlam (sub_nonneg.mpr hf.2.2)
  have hcoords : 0 ≤ ∑ i, coordSlack (m i) (u i) (e i) lam :=
    Finset.sum_nonneg (fun i _ => coordinate_slack_nonneg _ _ _ _ (hf.1 i) (hf.2.1 i))
  apply sub_nonneg.mp
  rw [dual_gap_identity]
  exact add_nonneg hbudget hcoords

theorem equality_certificate (m u e : I → ℝ) (R lam : ℝ)
    (hc : Complementary m u e R lam) : primal m e = dual u e R lam := by
  have hcoords : (∑ i, coordSlack (m i) (u i) (e i) lam) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    unfold coordSlack
    rw [(hc.2 i).1, (hc.2 i).2, add_zero]
  have hgap := dual_gap_identity m u e R lam
  rw [hc.1, hcoords, add_zero] at hgap
  exact (sub_eq_zero.mp hgap).symm

theorem equality_iff (m u e : I → ℝ) (R lam : ℝ)
    (hf : Feasible m u R) (hlam : 0 ≤ lam) :
    primal m e = dual u e R lam ↔ Complementary m u e R lam := by
  classical
  constructor
  · intro heq
    have hbudget : 0 ≤ lam * (R - ∑ i, m i) :=
      mul_nonneg hlam (sub_nonneg.mpr hf.2.2)
    have hpos : ∀ i, 0 ≤ (u i - m i) * pospart (e i - lam) :=
      fun i => mul_nonneg (sub_nonneg.mpr (hf.2.1 i)) (pospart_nonneg _)
    have hneg : ∀ i, 0 ≤ m i * negpart (e i - lam) :=
      fun i => mul_nonneg (hf.1 i) (negpart_nonneg _)
    have hterm : ∀ i, 0 ≤ coordSlack (m i) (u i) (e i) lam :=
      fun i => coordinate_slack_nonneg _ _ _ _ (hf.1 i) (hf.2.1 i)
    have hsum : 0 ≤ ∑ i, coordSlack (m i) (u i) (e i) lam :=
      Finset.sum_nonneg (fun i _ => hterm i)
    have hgap := dual_gap_identity m u e R lam
    rw [← heq, sub_self] at hgap
    have hbzero : lam * (R - ∑ i, m i) = 0 := by
      linarith only [hgap, hbudget, hsum]
    have hszero : (∑ i, coordSlack (m i) (u i) (e i) lam) = 0 := by
      linarith only [hgap, hbzero]
    refine ⟨hbzero, fun i => ?_⟩
    have hle : coordSlack (m i) (u i) (e i) lam ≤
        ∑ j, coordSlack (m j) (u j) (e j) lam :=
      Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
    rw [hszero] at hle
    have hi : coordSlack (m i) (u i) (e i) lam = 0 :=
      le_antisymm hle (hterm i)
    unfold coordSlack at hi
    exact ⟨by linarith only [hi, hpos i, hneg i],
      by linarith only [hi, hpos i, hneg i]⟩
  · exact equality_certificate m u e R lam

theorem threshold_optimal (m u e : I → ℝ) (R lam : ℝ)
    (hf : Feasible m u R) (hlam : 0 ≤ lam)
    (hbudget : lam = 0 ∨ (∑ i, m i) = R)
    (hhigh : ∀ i, lam < e i → m i = u i)
    (hlow : ∀ i, e i < lam → m i = 0)
    (m' : I → ℝ) (hf' : Feasible m' u R) :
    primal m' e ≤ primal m e := by
  have hc : Complementary m u e R lam := by
    constructor
    · rcases hbudget with hzero | hfull
      · rw [hzero, zero_mul]
      · rw [hfull, sub_self, mul_zero]
    · intro i
      constructor
      · by_cases hgt : lam < e i
        · rw [hhigh i hgt, sub_self, zero_mul]
        · have hnonpos : e i - lam ≤ 0 := sub_nonpos.mpr (le_of_not_gt hgt)
          simp [pospart, max_eq_right hnonpos]
      · by_cases hlt : e i < lam
        · rw [hlow i hlt, zero_mul]
        · have hnonpos : -(e i - lam) ≤ 0 :=
            neg_nonpos.mpr (sub_nonneg.mpr (le_of_not_gt hlt))
          simp [negpart, max_eq_right hnonpos]
  exact (dual_bound m' u e R lam hf' hlam).trans
    (le_of_eq (equality_certificate m u e R lam hc).symm)

end Finite

noncomputable def fixtureE : Fin 3 → ℝ := ![9, 5, 1]
noncomputable def fixtureU : Fin 3 → ℝ := ![2, 3, 4]
noncomputable def fixtureM : Fin 3 → ℝ := ![2, 2, 0]

theorem tight_fixture :
    Feasible fixtureM fixtureU 4 ∧
    primal fixtureM fixtureE = 28 ∧
    dual fixtureU fixtureE 4 5 = 28 ∧
    (28 : ℝ) < 36 ∧
    (∀ m' : Fin 3 → ℝ, Feasible m' fixtureU 4 → primal m' fixtureE ≤ 28) := by
  have hf : Feasible fixtureM fixtureU 4 := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num [fixtureM]
    · intro i
      fin_cases i <;> norm_num [fixtureM, fixtureU]
    · norm_num [fixtureM, Fin.sum_univ_succ]
  have hp : primal fixtureM fixtureE = 28 := by
    norm_num [primal, fixtureM, fixtureE, Fin.sum_univ_succ]
  have hd : dual fixtureU fixtureE 4 5 = 28 := by
    norm_num [dual, fixtureU, fixtureE, pospart, Fin.sum_univ_succ, max_def]
  refine ⟨hf, hp, hd, by norm_num, ?_⟩
  intro m' hf'
  have h := dual_bound m' fixtureU fixtureE 4 5 hf' (by norm_num)
  rwa [hd] at h

theorem missing_cap_control :
    ∃ (m u e : Unit → ℝ) (R lam : ℝ),
      (∀ i, 0 ≤ m i) ∧ (∑ i, m i) ≤ R ∧ 0 ≤ lam ∧
      (∃ i, u i < m i) ∧ dual u e R lam < primal m e := by
  refine ⟨fun _ => 2, fun _ => 1, fun _ => 1, 2, 0, ?_⟩
  refine ⟨fun _ => by norm_num, by norm_num, by norm_num, ⟨(), by norm_num⟩, ?_⟩
  norm_num [dual, primal, pospart]

theorem negative_multiplier_control :
    ∃ (m u e : Unit → ℝ) (R lam : ℝ),
      Feasible m u R ∧ lam < 0 ∧ dual u e R lam < primal m e := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, 1, -1, ?_⟩
  refine ⟨⟨fun _ => le_rfl, fun _ => le_rfl, by norm_num⟩, by norm_num, ?_⟩
  norm_num [dual, primal, pospart]

theorem negative_mass_control :
    ∃ (m u e : Unit → ℝ) (R lam : ℝ),
      (∀ i, m i ≤ u i) ∧ (∑ i, m i) ≤ R ∧ 0 ≤ lam ∧
      (∃ i, m i < 0) ∧ dual u e R lam < primal m e := by
  refine ⟨fun _ => -1, fun _ => 0, fun _ => -1, 0, 0, ?_⟩
  refine ⟨fun _ => by norm_num, by norm_num, by norm_num, ⟨(), by norm_num⟩, ?_⟩
  norm_num [dual, primal, pospart]

end RH26E04C

#print axioms RH26E04C.hinge_split
#print axioms RH26E04C.coordinate_gap
#print axioms RH26E04C.dual_gap_identity
#print axioms RH26E04C.dual_bound
#print axioms RH26E04C.equality_certificate
#print axioms RH26E04C.equality_iff
#print axioms RH26E04C.threshold_optimal
#print axioms RH26E04C.tight_fixture
#print axioms RH26E04C.missing_cap_control
#print axioms RH26E04C.negative_multiplier_control
#print axioms RH26E04C.negative_mass_control
