import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Finset

namespace CLN07A

def d (j : ℕ) : ℕ := 2^(j+2)
def m (j : ℕ) : ℕ := 2^(d j)

/-- This is the square-growth schedule with initial block start 16. -/
theorem m_zero : m 0 = 16 := by decide

theorem m_succ (j : ℕ) : m (j+1) = m j * m j := by
  have hd : d (j+1) = d j * 2 := by
    unfold d
    have he : j+1+2 = (j+2)+1 := by omega
    rw [he, pow_succ]
  change 2^(d (j+1)) = 2^(d j) * 2^(d j)
  rw [hd, pow_mul, pow_two]

theorem d_large (j : ℕ) : j+2 ≤ d j ∧ 4 ≤ d j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have he : d (j+1) = d j * 2 := by
      unfold d
      have h : j+1+2 = (j+2)+1 := by omega
      rw [h, pow_succ]
    rw [he]
    omega

theorem three_mul_le_pow (n : ℕ) (hn : 4 ≤ n) : 3*n ≤ 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : 4 ≤ n
    · have hh := ih h
      rw [pow_succ]
      omega
    · have he : n = 3 := by omega
      subst n
      decide

theorem entropy_exponent (j : ℕ) : 2*d j+j+2 ≤ m j := by
  have hd := d_large j
  have hh := three_mul_le_pow (d j) hd.2
  change 2*d j+j+2 ≤ 2^(d j)
  omega

theorem m_ge_sixteen (j : ℕ) : 16 ≤ m j := by
  change 2^4 ≤ 2^(d j)
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (d_large j).2

theorem block_gap (j : ℕ) : 2*m j < m (j+1) := by
  have h : 2 < m j := lt_of_lt_of_le (by decide) (m_ge_sixteen j)
  rw [m_succ]
  simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left h
    (lt_of_lt_of_le (by decide : 0 < 16) (m_ge_sixteen j))

/-- Free digits use one-based indices in the disjoint intervals (m_j,2m_j]. -/
def free (n : ℕ) : Prop := ∃ j : ℕ, m j < n ∧ n ≤ 2*m j

noncomputable def prefixEntropy (k : ℕ) : ℕ := by
  classical
  exact ((Finset.range (k+1)).filter free).card

/-- Every completed free block contributes m_j independent bits.
An explicit injection avoids any unstated interval-cardinality lemma. -/
theorem prefix_entropy_lower (j k : ℕ) (hk : 2*m j ≤ k) :
    m j ≤ prefixEntropy k := by
  classical
  unfold prefixEntropy
  have h := Finset.card_le_card_of_injOn
    (s := Finset.range (m j))
    (t := (Finset.range (k+1)).filter free)
    (fun i : ℕ => m j+i+1)
    (by
      intro i hi
      have hi' : i < m j := Finset.mem_range.mp hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), ⟨j, by omega, by omega⟩⟩)
    (by
      intro i hi l hl he
      omega)
  simpa using h

/-- Integer certificate for the full entropy cost of a block:
2*m_(j+1)*2^(j+1) <= 2^(m_j).
Dividing gives a geometric bound on the probability-mass sum. -/
theorem dyadic_block_budget (j : ℕ) :
    2*m (j+1)*2^(j+1) ≤ 2^(m j) := by
  have he := entropy_exponent j
  calc
    _ = 2^1 * (2^(d j) * 2^(d j)) * 2^(j+1) := by
      rw [m_succ]
      simp [m]
    _ = 2^(1+d j+d j+(j+1)) := by simp only [pow_add]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)

/-- Any prefix beyond the completed block inherits its dyadic budget. -/
theorem prefix_block_budget (j k : ℕ) (hk : 2*m j ≤ k) :
    2*m (j+1)*2^(j+1) ≤ 2^(prefixEntropy k) :=
  (dyadic_block_budget j).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (prefix_entropy_lower j k hk))

#print axioms m_zero
#print axioms m_succ
#print axioms d_large
#print axioms three_mul_le_pow
#print axioms entropy_exponent
#print axioms m_ge_sixteen
#print axioms block_gap
#print axioms prefix_entropy_lower
#print axioms dyadic_block_budget
#print axioms prefix_block_budget

end CLN07A
