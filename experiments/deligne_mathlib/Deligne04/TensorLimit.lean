import Deligne04.PowerLimit
import Deligne04.AllPowers
import Mathlib.Tactic

/-!
# DEL-05: the k-indexed spectral form of Lemma 2

This is an exact abstract interface for the analytic/spectral content of
Hexagon 2611.00789v1, Lemma 2 (page 4). The explicit hypotheses for
each admissible k include:
  * a positive finite-extension degree e_k;
  * an actual finite spectrum with distinct values and nonzero weights;
  * a spectral occurrence of alpha^(k*e_k);
  * a signed trace identity for every n >= 1;
  * a uniform-in-n point-count error estimate;
  * a relative exponent loss c_k/k tending to zero.
The geometric construction of those modules is kept as an external
premise. Every claim below is conditional on that interface.
-/

open Filter

namespace Deligne05

/-- An abstract k-indexed spectral version of Lemma 2.
The index j enumerates admissible tensor powers k(j); the extension
degrees e(j) and auxiliary spectra may change on every index. -/
theorem indexed_spectral_bound
    {s : ℕ → ℕ}
    (q a : ℝ) (hq : 0 < q) (alpha : ℂ)
    (k e : ℕ → ℕ) (c C : ℕ → ℝ)
    (lam weights : (j : ℕ) → Fin (s j) → ℂ)
    (eps : ℕ → ℂ) (R : ℕ → ℕ → ℂ)
    (hk : ∀ j, 0 < k j) (he : ∀ j, 0 < e j)
    (herr : Tendsto (fun j => c j / (k j : ℝ)) atTop (nhds 0))
    (hinj : ∀ j, Function.Injective (lam j))
    (hw : ∀ j i, weights j i ≠ 0)
    (hfound : ∀ j, ∃ i : Fin (s j),
      lam j i = alpha ^ (k j * e j))
    (heps : ∀ j, ‖eps j‖ = 1)
    (hidentity : ∀ j n, 0 < n →
      eps j * R j n = Deligne04.powerTrace (lam j) (weights j) n)
    (hR : ∀ j n, 0 < n →
      ‖R j n‖ ≤ C j *
        (q ^ ((e j : ℝ) * ((k j : ℝ) * a + c j))) ^ n) :
    ‖alpha‖ ≤ q ^ a := by
  apply exponent_budget_limit hq (norm_nonneg alpha) k e c hk he herr
  intro j
  let B : ℝ := q ^ ((e j : ℝ) * ((k j : ℝ) * a + c j))
  have hB : 0 < B := Real.rpow_pos_of_pos hq _
  have ht : ∀ n : ℕ, 0 < n →
      ‖Deligne04.powerTrace (lam j) (weights j) n‖ ≤
        C j * B ^ n := by
    intro n hn
    calc
      ‖Deligne04.powerTrace (lam j) (weights j) n‖ =
          ‖eps j * R j n‖ :=
            congrArg norm (hidentity j n hn).symm
      _ = ‖R j n‖ := by rw [norm_mul, heps j, one_mul]
      _ ≤ C j * B ^ n := by simpa [B] using hR j n hn
  have hs := Deligne04.finite_spectral_power_bound_pos
    (lam j) (weights j) (hinj j) (hw j) hB ht
  obtain ⟨i, hi⟩ := hfound j
  have hb := hs i
  rw [hi, norm_pow] at hb
  exact hb

/-- Paper-facing specialization: the weights are positive integer
multiplicities and each sign is explicitly +1 or -1. The strict
monotonicity of k certifies infinitely many distinct admissible
tensor powers; the proof itself uses only their relative-error limit. -/
theorem indexed_spectral_bound_integer_multiplicity
    {s : ℕ → ℕ}
    (q a : ℝ) (hq : 1 < q) (alpha : ℂ)
    (k e : ℕ → ℕ) (c C : ℕ → ℝ)
    (lam : (j : ℕ) → Fin (s j) → ℂ)
    (m : (j : ℕ) → Fin (s j) → ℕ)
    (eps : ℕ → ℂ) (R : ℕ → ℕ → ℂ)
    (hks : StrictMono k)
    (hk : ∀ j, 0 < k j) (he : ∀ j, 0 < e j)
    (hc : ∀ j, 0 ≤ c j) (hC : ∀ j, 0 < C j)
    (herr : Tendsto (fun j => c j / (k j : ℝ)) atTop (nhds 0))
    (hinj : ∀ j, Function.Injective (lam j))
    (hm : ∀ j i, 0 < m j i)
    (hfound : ∀ j, ∃ i : Fin (s j),
      lam j i = alpha ^ (k j * e j))
    (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (hidentity : ∀ j n, 0 < n →
      eps j * R j n = Deligne04.powerTrace (lam j)
        (fun i => (m j i : ℂ)) n)
    (hR : ∀ j n, 0 < n →
      ‖R j n‖ ≤ C j *
        (q ^ ((e j : ℝ) * ((k j : ℝ) * a + c j))) ^ n) :
    ‖alpha‖ ≤ q ^ a := by
  have hunit : ∀ j, ‖eps j‖ = 1 := by
    intro j
    rcases heps j with hj | hj
    · simp [hj]
    · simp [hj]
  have hmult : ∀ j i, (m j i : ℂ) ≠ 0 := by
    intro j i
    exact_mod_cast (Nat.ne_of_gt (hm j i))
  exact indexed_spectral_bound q a (lt_trans zero_lt_one hq)
    alpha k e c C lam (fun j i => (m j i : ℂ)) eps R
    hk he herr hinj hmult hfound hunit hidentity hR

#print axioms indexed_spectral_bound
#print axioms indexed_spectral_bound_integer_multiplicity

end Deligne05
