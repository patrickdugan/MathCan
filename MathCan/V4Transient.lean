import MathCan.FlashAccounting

/-!
# CHTR-07: a finite-support ghost invariant for Uniswap v4 NonzeroDeltaCount

A declared transient delta map is represented by a finite list of signed
integers, with one position for each observed (caller, currency) pair. Updating
one entry changes the nonzero count by its indicator difference. This is an
accounting refinement obligation for PoolManager's `_accountDelta`; it does not
certify that an external EVM transcript enumerates every slot or call frame.
-/
namespace MathCan.V4Transient

/-- Count contribution of a signed transient delta (a ghost value, not an EVM slot). -/
def nz (x : Int) : Int := if x = 0 then 0 else 1

/-- Finite list model of NonzeroDeltaCount. -/
def count : List Int → Int
  | [] => 0
  | x :: xs => nz x + count xs

theorem nz_nonnegative (x : Int) : 0 ≤ nz x := by
  unfold nz
  split <;> omega

theorem nz_zero_iff (x : Int) : nz x = 0 ↔ x = 0 := by
  by_cases h : x = 0 <;> simp [nz, h]

theorem count_nonnegative (xs : List Int) : 0 ≤ count xs := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
      have hn := nz_nonnegative x
      simp only [count]
      omega

theorem count_append (left right : List Int) :
    count (left ++ right) = count left + count right := by
  induction left with
  | nil => simp [count]
  | cons x xs ih =>
      simp only [List.cons_append, count, ih]
      omega

/-- Replacing one currency-delta slot changes the global count by a local
    zero-crossing difference, independently of the surrounding slots. -/
theorem count_replace (prefix suffix : List Int) (old next : Int) :
    count (prefix ++ next :: suffix) =
      count (prefix ++ old :: suffix) + (nz next - nz old) := by
  simp only [count_append, count]
  omega

/-- The source's increment/decrement cases agree with the ghost count. -/
theorem zero_crossing_equivalence (old next : Int) :
    nz next - nz old =
      (if old = 0 ∧ next ≠ 0 then (1 : Int)
       else if old ≠ 0 ∧ next = 0 then (-1 : Int) else 0) := by
  by_cases hOld : old = 0 <;> by_cases hNext : next = 0 <;>
    simp [nz, hOld, hNext]

/-- A locally correct count update preserves correctness for the whole
    finite support, including nonzero to nonzero transitions. -/
theorem count_update_correct (prefix suffix : List Int)
    (old next oldCounter : Int)
    (h : oldCounter = count (prefix ++ old :: suffix)) :
    oldCounter + nz next - nz old =
      count (prefix ++ next :: suffix) := by
  have hs := count_replace prefix suffix old next
  rw [h]
  omega

/-- If the ghost count is zero, every member of the declared delta support
    is zero. -/
theorem count_zero_all :
    ∀ (xs : List Int), count xs = 0 → ∀ x, x ∈ xs → x = 0 := by
  intro xs
  induction xs with
  | nil =>
      intro _ x hx
      cases hx
  | cons y ys ih =>
      intro h x hx
      have hNonneg := count_nonnegative ys
      have hNzNonneg := nz_nonnegative y
      have hs : nz y + count ys = 0 := by simpa only [count] using h
      have hyNz : nz y = 0 := by omega
      have ht : count ys = 0 := by omega
      have hy : y = 0 := (nz_zero_iff y).mp hyNz
      rcases List.mem_cons.mp hx with heq | rest
      · rw [heq]
        exact hy
      · exact ih ht x rest

/-- Kernel-level lock obligation for the complete observed support. -/
theorem lock_zero_count (slots : List Int) (reportedCount : Int)
    (hCount : reportedCount = count slots)
    (hLock : reportedCount = 0) :
    ∀ x, x ∈ slots → x = 0 := by
  exact count_zero_all slots (by omega)

/-- A paid ERC20 balance difference is fixed by the synced snapshot. -/
theorem erc20_paid_exact (before now paid : Int)
    (h : now = before + paid) : now - before = paid := by
  omega

/-- A native-currency call can credit only its attached msg.value. -/
theorem native_credit_exact (msgValue paid : Int)
    (h : paid = msgValue) : paid - msgValue = 0 := by
  omega

#print axioms nz_nonnegative
#print axioms nz_zero_iff
#print axioms count_nonnegative
#print axioms count_append
#print axioms count_replace
#print axioms zero_crossing_equivalence
#print axioms count_update_correct
#print axioms count_zero_all
#print axioms lock_zero_count
#print axioms erc20_paid_exact
#print axioms native_credit_exact

end MathCan.V4Transient
