import Deligne04.AllPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-!
# DEL-05: extension-degree cancellation and cofinal exponent limit

These results isolate the real-analytic component of Lemma 2 in
Hexagon 2611.00789v1, p. 4. The k-indexed Frobenius spectral
interface is developed separately in TensorLimit.lean.
-/

open Filter

namespace Deligne05

/-- The extension degree e cancels from the k-th tensor-power bound.
The proof works even when the extension degree changes with k. -/
theorem cancel_extension_degree
    {q r a c : ℝ} {k e : ℕ}
    (hq : 0 < q) (hr : 0 ≤ r)
    (hk : 0 < k) (he : 0 < e)
    (hbound : r ^ (k * e) ≤
      q ^ ((e : ℝ) * ((k : ℝ) * a + c))) :
    r ≤ q ^ (a + c / (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hke : (0 : ℝ) < ((k * e : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos hk he)
  have hexp :
      (a + c / (k : ℝ)) * ((k * e : ℕ) : ℝ) =
        (e : ℝ) * ((k : ℝ) * a + c) := by
    push_cast
    field_simp [hk0]
    ring
  have hpow :
      r ^ (((k * e : ℕ) : ℝ)) ≤
        (q ^ (a + c / (k : ℝ))) ^ (((k * e : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hq), hexp]
    exact hbound
  exact (Real.rpow_le_rpow_iff hr
    (Real.rpow_nonneg (le_of_lt hq) _) hke).mp hpow

/-- If the relative exponent errors converge to zero, every uniform
upper bound q^(a+error_j) passes to q^a in the limit. -/
theorem relative_error_limit
    {q r a : ℝ} (hq : 0 < q) (hr : 0 < r)
    {err : ℕ → ℝ}
    (herr : Tendsto err atTop (nhds 0))
    (hbound : ∀ j, r ≤ q ^ (a + err j)) :
    r ≤ q ^ a := by
  have hadd : Tendsto (fun j : ℕ => a + err j)
      atTop (nhds (a + 0)) := tendsto_const_nhds.add herr
  have ht : Tendsto (fun j : ℕ =>
      (a + err j) * Real.log q) atTop
      (nhds (a * Real.log q)) := by
    simpa using hadd.mul_const (Real.log q)
  have hlog : ∀ j : ℕ,
      Real.log r ≤ (a + err j) * Real.log q := by
    intro j
    exact (Real.le_rpow_iff_log_le hr hq).mp (hbound j)
  have hlim : Real.log r ≤ a * Real.log q :=
    ge_of_tendsto ht (Eventually.of_forall hlog)
  exact (Real.le_rpow_iff_log_le hr hq).mpr hlim

/-- The fully assembled scalar cancellation and limit, with a
separate extension degree for each certified index. -/
theorem exponent_budget_limit
    {q r a : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (k e : ℕ → ℕ) (c : ℕ → ℝ)
    (hk : ∀ j, 0 < k j) (he : ∀ j, 0 < e j)
    (herr : Tendsto (fun j => c j / (k j : ℝ)) atTop (nhds 0))
    (hbound : ∀ j,
      r ^ (k j * e j) ≤
        q ^ ((e j : ℝ) * ((k j : ℝ) * a + c j))) :
    r ≤ q ^ a := by
  by_cases hr0 : r = 0
  · subst r
    exact (Real.rpow_pos_of_pos hq a).le
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    exact relative_error_limit hq hrpos herr
      (fun j => cancel_extension_degree hq hr
        (hk j) (he j) (hbound j))

#print axioms cancel_extension_degree
#print axioms relative_error_limit
#print axioms exponent_budget_limit

end Deligne05
