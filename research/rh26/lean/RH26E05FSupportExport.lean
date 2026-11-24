import Mathlib

/-!
Independent support-preserving valuation export, motivated by the finite
prime-wise assembly in RH26B14. Arrays below are already log-weighted.
The upstream arithmetic bounds are explicit premises.
-/

namespace RH26E05F

open scoped BigOperators

section Finite

variable {I : Type*}

theorem finite_aggregation (S : Finset I)
    (eta e nu lam vv h g : I → ℝ) (R : ℝ)
    (hp : ∀ i ∈ S, eta i ≤ R * (2 * e i + nu i + lam i + vv i + h i + g i)) :
    (∑ i ∈ S, eta i) ≤ R * ∑ i ∈ S, (2 * e i + nu i + lam i + vv i + h i + g i) := by
  calc
    _ ≤ ∑ i ∈ S, R * (2 * e i + nu i + lam i + vv i + h i + g i) :=
      Finset.sum_le_sum hp
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem signature_budget (S : Finset I) (e nu : I → ℝ) (Bnu : ℝ)
    (he : (∑ i ∈ S, e i) ≤ 2) (hnu : (∑ i ∈ S, nu i) ≤ Bnu) :
    (∑ i ∈ S, (2 * e i + nu i)) ≤ 4 + Bnu := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith only [he, hnu]

theorem finite_support_bound (S : Finset I)
    (eta e nu lam vv h g : I → ℝ) (R Bnu Bh Bg : ℝ)
    (hR : 0 ≤ R)
    (hp : ∀ i ∈ S, eta i ≤ R * (2 * e i + nu i + lam i + vv i + h i + g i))
    (he : (∑ i ∈ S, e i) ≤ 2) (hnu : (∑ i ∈ S, nu i) ≤ Bnu)
    (hh : (∑ i ∈ S, h i) ≤ Bh) (hg : (∑ i ∈ S, g i) ≤ Bg) :
    (∑ i ∈ S, eta i) ≤
      R * (4 + Bnu + Bh + Bg + (∑ i ∈ S, lam i) + (∑ i ∈ S, vv i)) := by
  apply (finite_aggregation S eta e nu lam vv h g R hp).trans
  apply mul_le_mul_of_nonneg_left _ hR
  have hs := signature_budget S e nu Bnu he hnu
  simp only [Finset.sum_add_distrib] at hs ⊢
  linarith only [hs, hh, hg]

theorem finite_export (S : Finset I)
    (eta e nu lam vv h g : I → ℝ) (R Bnu Bh Bg K X : ℝ)
    (hR : 0 ≤ R)
    (hp : ∀ i ∈ S, eta i ≤ R * (2 * e i + nu i + lam i + vv i + h i + g i))
    (he : (∑ i ∈ S, e i) ≤ 2) (hnu : (∑ i ∈ S, nu i) ≤ Bnu)
    (hh : (∑ i ∈ S, h i) ≤ Bh) (hg : (∑ i ∈ S, g i) ≤ Bg)
    (hpoint : 6 + Bnu + Bh + Bg + (∑ i ∈ S, lam i) ≤ K * X) :
    (∑ i ∈ S, eta i) ≤ R * (K * X - 2 + ∑ i ∈ S, vv i) := by
  apply (finite_support_bound S eta e nu lam vv h g R Bnu Bh Bg hR hp he hnu hh hg).trans
  apply mul_le_mul_of_nonneg_left _ hR
  linarith only [hpoint]

end Finite

noncomputable def tail {I : Type*} (S : Finset I) (v : I → ℝ) : ℝ :=
  (∑' i, v i) - ∑ i ∈ S, v i

theorem nonnegative_tail {I : Type*} (S : Finset I) (v : I → ℝ)
    (hs : Summable v) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ tail S v := by
  unfold tail
  exact sub_nonneg.mpr (Summable.sum_le_tsum S (fun i _ => hv i) hs)

theorem tail_identity {I : Type*} (S : Finset I) (v : I → ℝ) :
    (∑' i, v i) = (∑ i ∈ S, v i) + tail S v := by
  unfold tail
  ring

theorem padding_slack_identity (R K X N V F : ℝ) :
    R * (K * (X + N) + V) - R * (K * X - 2 + F) =
      R * (2 + (V - F) + K * N) := by
  ring

theorem padding_slack_nonneg {I : Type*} (S : Finset I) (v : I → ℝ)
    (R K X N : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hs : Summable v) (hv : ∀ i, 0 ≤ v i) :
    R * (K * X - 2 + ∑ i ∈ S, v i) ≤ R * (K * (X + N) + ∑' i, v i) ∧
    R * (K * (X + N) + ∑' i, v i) - R * (K * X - 2 + ∑ i ∈ S, v i) =
      R * (2 + tail S v + K * N) := by
  have hgap :
      R * (K * (X + N) + ∑' i, v i) - R * (K * X - 2 + ∑ i ∈ S, v i) =
        R * (2 + tail S v + K * N) :=
    padding_slack_identity R K X N (∑' i, v i) (∑ i ∈ S, v i)
  refine ⟨?_, hgap⟩
  apply sub_nonneg.mp
  rw [hgap]
  have ht := nonnegative_tail S v hs hv
  have hp := mul_nonneg hK hN
  exact mul_nonneg hR (by linarith only [ht, hp])

theorem combined_export {I : Type*} (S : Finset I)
    (eta e nu lam vv h g : I → ℝ) (R Bnu Bh Bg K X N : ℝ)
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hp : ∀ i ∈ S, eta i ≤ R * (2 * e i + nu i + lam i + vv i + h i + g i))
    (he : (∑ i ∈ S, e i) ≤ 2) (hnu : (∑ i ∈ S, nu i) ≤ Bnu)
    (hh : (∑ i ∈ S, h i) ≤ Bh) (hg : (∑ i ∈ S, g i) ≤ Bg)
    (hpoint : 6 + Bnu + Bh + Bg + (∑ i ∈ S, lam i) ≤ K * X)
    (hs : Summable vv) (hv : ∀ i, 0 ≤ vv i) :
    (∑ i ∈ S, eta i) ≤ R * (K * X - 2 + ∑ i ∈ S, vv i) ∧
    (∑ i ∈ S, eta i) ≤ R * (K * (X + N) + ∑' i, vv i) := by
  have hf := finite_export S eta e nu lam vv h g R Bnu Bh Bg K X
    hR hp he hnu hh hg hpoint
  exact ⟨hf, hf.trans (padding_slack_nonneg S vv R K X N hR hK hN hs hv).1⟩

noncomputable def positiveFixture (i : Fin 2) : ℝ :=
  if i = 0 then 2 else 3

noncomputable def signedFixture (i : Fin 2) : ℝ :=
  if i = 0 then 2 else -3

theorem nonnegative_tail_fixture :
    (∑ i ∈ ({0} : Finset (Fin 2)), positiveFixture i) = 2 ∧
    (∑' i, positiveFixture i) = 5 ∧
    tail ({0} : Finset (Fin 2)) positiveFixture = 3 := by
  norm_num [tail, positiveFixture, tsum_fintype, Fin.sum_univ_two]

theorem signed_tail_control :
    Summable signedFixture ∧
    (∑ i ∈ ({0} : Finset (Fin 2)), signedFixture i) = 2 ∧
    (∑' i, signedFixture i) = -1 ∧
    tail ({0} : Finset (Fin 2)) signedFixture = -3 ∧
    (∑' i, signedFixture i) < ∑ i ∈ ({0} : Finset (Fin 2)), signedFixture i := by
  have hs : Summable signedFixture := (hasSum_fintype signedFixture).summable
  refine ⟨hs, ?_⟩
  norm_num [tail, signedFixture, tsum_fintype, Fin.sum_univ_two]

theorem nonsummable_support_control :
    ¬ Summable (fun _ : ℕ => (1 : ℝ)) ∧
    (∀ S : Finset ℕ, (∑ i ∈ S, (1 : ℝ)) = (S.card : ℝ)) ∧
    (∑ i ∈ ({0} : Finset ℕ), (1 : ℝ)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    obtain ⟨n, hn⟩ := exists_nat_gt (∑' _ : ℕ, (1 : ℝ))
    have hh := Summable.sum_le_tsum (Finset.range n) (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) hs
    have hle : (n : ℝ) ≤ ∑' _ : ℕ, (1 : ℝ) := by
      simpa using hh
    exact (not_lt_of_ge hle) hn
  · intro S
    simp
  · simp

end RH26E05F

#print axioms RH26E05F.finite_aggregation
#print axioms RH26E05F.signature_budget
#print axioms RH26E05F.finite_support_bound
#print axioms RH26E05F.finite_export
#print axioms RH26E05F.nonnegative_tail
#print axioms RH26E05F.tail_identity
#print axioms RH26E05F.padding_slack_identity
#print axioms RH26E05F.padding_slack_nonneg
#print axioms RH26E05F.combined_export
#print axioms RH26E05F.nonnegative_tail_fixture
#print axioms RH26E05F.signed_tail_control
#print axioms RH26E05F.nonsummable_support_control
