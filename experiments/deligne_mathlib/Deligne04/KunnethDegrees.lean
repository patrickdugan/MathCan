import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# DEL-06: uniqueness of the lowest Künneth degree

If every tensor factor vanishes below degree d, then the only
k-tuple of degrees reaching total kd is the constant tuple d.
This supplies the combinatorial component of Proposition 4's
identification of the lowest compactly supported cohomology.
The actual Künneth theorem and vanishing of sheaf cohomology
remain separate geometric inputs.
-/

open scoped BigOperators
open Finset

namespace Deligne06

/-- In a k-fold tensor Künneth decomposition, factors at least
in degree d can sum to kd only when all degrees equal d. -/
theorem lowest_kunneth_degrees_unique
    (d k : ℕ) (degrees : Fin k → ℕ)
    (hlower : ∀ i, d ≤ degrees i)
    (hsum : (∑ i : Fin k, degrees i) = k * d) :
    ∀ i : Fin k, degrees i = d := by
  have hsum_int :
      (∑ i : Fin k, (degrees i : ℤ)) = (k : ℤ) * (d : ℤ) := by
    exact_mod_cast hsum
  have hdiff :
      (∑ i : Fin k, ((degrees i : ℤ) - (d : ℤ))) = 0 := by
    simp [Finset.sum_sub_distrib, hsum_int]
  have hnonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin k)),
        (0 : ℤ) ≤ (degrees i : ℤ) - (d : ℤ) := by
    intro i _
    exact sub_nonneg.mpr (by exact_mod_cast hlower i)
  have hzero :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdiff
  intro i
  have hi := hzero i (Finset.mem_univ i)
  omega

/-- A proposed mixed-degree contribution is excluded immediately
when any factor falls below d. -/
theorem mixed_kunneth_degree_excluded
    (d k : ℕ) (degrees : Fin k → ℕ)
    (hbelow : ∃ i, degrees i < d) :
    ¬ (∀ i, d ≤ degrees i) := by
  intro h
  obtain ⟨i, hi⟩ := hbelow
  exact (not_le_of_gt hi) (h i)

#print axioms lowest_kunneth_degrees_unique
#print axioms mixed_kunneth_degree_excluded

end Deligne06
