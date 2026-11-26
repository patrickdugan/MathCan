module

public import TRR08Geometry.RootCardinality

/-!
# Finite residue annihilation of polynomial normal forms

The original residue functional cancels the even part under inversion.
Its odd part is the Lagrange leading coefficient on the distinct x-roots.
The proof uses actual subgroup points and their inverse-product residues.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K} [W.IsShortNF]

noncomputable def residueSum (H : AddSubgroup W.Point) [Fintype H] (f : H → K) : K :=
  ∑ P : H, subgroupResidue H P * f P

omit [W.IsShortNF] in
theorem residueSum_add (H : AddSubgroup W.Point) [Fintype H] (f g : H → K) :
    residueSum H (fun P => f P + g P) = residueSum H f + residueSum H g := by
  simp [residueSum, mul_add, Finset.sum_add_distrib]

omit [W.IsShortNF] in
theorem residueSum_const_mul (H : AddSubgroup W.Point) [Fintype H]
    (c : K) (f : H → K) :
    residueSum H (fun P => c * f P) = c * residueSum H f := by
  unfold residueSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  ring

theorem residueSum_congr_nonzero (H : AddSubgroup W.Point) [Fintype H]
    (f g : H → K) (hfg : ∀ P : H, P ≠ 0 → f P = g P) :
    residueSum H f = residueSum H g := by
  classical
  apply Finset.sum_congr rfl
  intro P _
  by_cases hP : P = 0
  · subst P
    simp
  · rw [hfg P hP]

theorem residueSum_xFunction (H : AddSubgroup W.Point) [Fintype H]
    (h₂ : (2 : K) ≠ 0) (f : K → K) :
    residueSum H (fun P => f (affineX (P : W.Point))) = 0 := by
  have hn :
      (∑ P : H, subgroupResidue H (-P) * f (affineX ((-P : H) : W.Point))) =
      ∑ P : H, subgroupResidue H P * f (affineX (P : W.Point)) := by
    exact Fintype.sum_equiv (Equiv.neg H)
      (fun P => subgroupResidue H (-P) * f (affineX ((-P : H) : W.Point)))
      (fun P => subgroupResidue H P * f (affineX (P : W.Point))) (fun _ => rfl)
  simp only [AddSubgroup.coe_neg, affineX_neg, subgroupResidue_neg, neg_mul,
    Finset.sum_neg_distrib] at hn
  change -residueSum H (fun P => f (affineX (P : W.Point))) =
    residueSum H (fun P => f (affineX (P : W.Point))) at hn
  have hz : 2 * residueSum H (fun P => f (affineX (P : W.Point))) = 0 := by
    linear_combination -hn
  exact (mul_eq_zero.mp hz).resolve_left h₂

theorem residueSum_yFunction (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0) (f : K → K) :
    residueSum H (fun P => affineY (P : W.Point) * f (affineX (P : W.Point))) =
      ∑ v ∈ subgroupXRoots H, subgroupNodalWeight H v * f v := by
  classical
  apply mul_left_cancel₀ h₂
  unfold residueSum
  calc
    2 * (∑ P : H, subgroupResidue H P *
        (affineY (P : W.Point) * f (affineX (P : W.Point)))) =
        ∑ P : H, 2 * (subgroupResidue H P *
          (affineY (P : W.Point) * f (affineX (P : W.Point)))) := Finset.mul_sum _ _ _
    _ = ∑ P ∈ Finset.univ.erase (0 : H), 2 * (subgroupResidue H P *
          (affineY (P : W.Point) * f (affineX (P : W.Point)))) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : H))]
      simp
    _ = ∑ P ∈ Finset.univ.erase (0 : H),
        subgroupNodalWeight H (affineX (P : W.Point)) * f (affineX (P : W.Point)) := by
      apply Finset.sum_congr rfl
      intro P hP
      have hp : P ≠ 0 := (Finset.mem_erase.mp hP).1
      have hp' : (P : W.Point) ≠ 0 := fun h => hp (Subtype.ext h)
      have hd : (P : W.Point) + (P : W.Point) ≠ 0 := by
        intro h
        exact hno2 P hp (eq_neg_iff_add_eq_zero.mpr (Subtype.ext h))
      have hy := short_y_ne_zero hp' hd
      unfold subgroupResidue
      field_simp
    _ = 2 • (∑ v ∈ subgroupXRoots H, subgroupNodalWeight H v * f v) :=
      subgroupNonzero_sum_by_roots H hno2 (fun v => subgroupNodalWeight H v * f v)
    _ = 2 * (∑ v ∈ subgroupXRoots H, subgroupNodalWeight H v * f v) := by
      simp only [nsmul_eq_mul, Nat.cast_ofNat]

theorem residueSum_normalForm (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0)
    (p q : K[X]) :
    residueSum H (fun P => p.eval (affineX (P : W.Point)) +
      affineY (P : W.Point) * q.eval (affineX (P : W.Point))) =
      ∑ v ∈ subgroupXRoots H, subgroupNodalWeight H v * q.eval v := by
  rw [residueSum_add, residueSum_xFunction H h₂ (fun v => p.eval v), zero_add]
  exact residueSum_yFunction H hno2 h₂ (fun v => q.eval v)

omit [W.IsShortNF] in
theorem subgroupNodalWeight_eval_sum_eq_coeff (H : AddSubgroup W.Point) [Fintype H]
    (q : K[X]) (hq : q.degree < (subgroupXRoots H).card) :
    (∑ v ∈ subgroupXRoots H, subgroupNodalWeight H v * q.eval v) =
      q.coeff ((subgroupXRoots H).card - 1) := by
  have he := Lagrange.coeff_eq_sum (s := subgroupXRoots H) (v := id)
    (P := q) (fun _ _ _ _ h => h) hq
  rw [he]
  apply Finset.sum_congr rfl
  intro v _
  simp [subgroupNodalWeight, Lagrange.nodalWeight, div_eq_mul_inv,
    Finset.prod_inv_distrib, mul_comm]

theorem residueSum_normalForm_eq_coeff (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0)
    (p q : K[X]) (hq : q.degree < (subgroupXRoots H).card) :
    residueSum H (fun P => p.eval (affineX (P : W.Point)) +
      affineY (P : W.Point) * q.eval (affineX (P : W.Point))) =
      q.coeff ((subgroupXRoots H).card - 1) := by
  rw [residueSum_normalForm H hno2 h₂ p q]
  exact subgroupNodalWeight_eval_sum_eq_coeff H q hq

theorem residueSum_normalForm_eq_zero (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (h₂ : (2 : K) ≠ 0)
    (p q : K[X]) (hq : q.degree < ((subgroupXRoots H).card - 1 : ℕ)) :
    residueSum H (fun P => p.eval (affineX (P : W.Point)) +
      affineY (P : W.Point) * q.eval (affineX (P : W.Point))) = 0 := by
  have hq' : q.degree < (subgroupXRoots H).card :=
    lt_of_lt_of_le hq (by exact_mod_cast Nat.sub_le (subgroupXRoots H).card 1)
  rw [residueSum_normalForm_eq_coeff H hno2 h₂ p q hq']
  exact Polynomial.coeff_eq_zero_of_degree_lt hq

end TRR08Geometry

#print axioms TRR08Geometry.residueSum_add
#print axioms TRR08Geometry.residueSum_const_mul
#print axioms TRR08Geometry.residueSum_congr_nonzero
#print axioms TRR08Geometry.residueSum_xFunction
#print axioms TRR08Geometry.residueSum_yFunction
#print axioms TRR08Geometry.residueSum_normalForm
#print axioms TRR08Geometry.subgroupNodalWeight_eval_sum_eq_coeff
#print axioms TRR08Geometry.residueSum_normalForm_eq_coeff
#print axioms TRR08Geometry.residueSum_normalForm_eq_zero
