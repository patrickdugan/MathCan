import Mathlib.Tactic

/-!
# DEL-07: degree bookkeeping for Katz A.5 and Poincare duality

The perverse sheaf is the shifted lisse sheaf G[D]. Katz A.5
gives an isomorphism for perverse degree i < -1 and injectivity
for i = -1. The ordinary degree is a = D + i. Poincare duality
turns restriction in ordinary degree a into a Gysin map from
compact degree j = 2*D-2-a on the hypersurface to degree j+2
on the D-dimensional ambient variety.

These are formal integer arithmetic deductions from the named
perverse/Lefschetz and duality hypotheses. The existence of
the schemes, perverse sheaves and duality functors remains external.
-/

namespace Deligne07

/-- The shifted perverse cut-off i<-1 becomes a<D-1. -/
theorem katz_shift_iso_degree {D a i : ℤ}
    (hshift : a = D + i) (hi : i < -1) :
    a < D - 1 := by
  omega

/-- Katz's boundary i=-1 becomes ordinary degree a=D-1. -/
theorem katz_shift_boundary_degree {D a i : ℤ}
    (hshift : a = D + i) (hi : i = -1) :
    a = D - 1 := by
  omega

/-- Duality for a codimension-one embedding transfers restriction
from ordinary degree a to the compactly supported Gysin degree
j = 2D-2-a. -/
theorem gysin_compact_degree_formula {D a j : ℤ}
    (hj : j = 2 * D - 2 - a) :
    j + 2 = 2 * D - a := by
  omega

/-- A strict degree in Katz's isomorphism range produces the
higher compact-degree isomorphism j>D-1. -/
theorem katz_iso_implies_high_gysin_degree {D a j : ℤ}
    (ha : a < D - 1)
    (hj : j = 2 * D - 2 - a) :
    D - 1 < j := by
  omega

/-- At the borderline ordinary restriction degree a=D-1,
the corresponding Gysin source is j=D-1 and target j+2=D+1. -/
theorem katz_injection_to_boundary_gysin_degree
    {D a j : ℤ}
    (ha : a = D - 1)
    (hj : j = 2 * D - 2 - a) :
    j = D - 1 ∧ j + 2 = D + 1 := by
  omega

/-- Both low and boundary degree translations together, starting
from the exact Katz perverse shift. -/
theorem katz_to_gysin_iso_cutoff {D a i j : ℤ}
    (hshift : a = D + i)
    (hi : i < -1)
    (hj : j = 2 * D - 2 - a) :
    D - 1 < j ∧ j + 2 = 2 * D - a := by
  exact ⟨katz_iso_implies_high_gysin_degree
      (katz_shift_iso_degree hshift hi) hj,
    gysin_compact_degree_formula hj⟩

/-- The Poincare dual of compact cohomology in dimension D
uses q^D times inverse ordinary Frobenius. In codimension one,
H_c(Y)(-1) has the same factor: q*q^(D-1)=q^D. -/
theorem codimension_one_tate_balance (q : ℂ) (d : ℕ) :
    q * q ^ d = q ^ (d + 1) := by
  rw [pow_succ]
  ring

#print axioms codimension_one_tate_balance

/-- A missing Tate twist would change Frobenius weights:
for an extension field of cardinality r, the (-1) twist has
Frobenius r, and the twist of F^n has eigenvalue r^n. -/
theorem tate_twist_scalar_power (r lambda : ℂ) (n : ℕ) :
    (r * lambda) ^ n = r ^ n * lambda ^ n := by
  rw [mul_pow]

#print axioms katz_shift_iso_degree
#print axioms katz_shift_boundary_degree
#print axioms gysin_compact_degree_formula
#print axioms katz_iso_implies_high_gysin_degree
#print axioms katz_injection_to_boundary_gysin_degree
#print axioms katz_to_gysin_iso_cutoff
#print axioms tate_twist_scalar_power

end Deligne07
