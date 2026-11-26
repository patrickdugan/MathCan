module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Finite barycentric identities at a node

Differentiate the actual Lagrange partition of unity. The identities below
give the first two regular coefficients of the partial-fraction expansion
at a chosen node, using finite sums and polynomial derivatives.
-/

namespace TRR08Geometry.BarycentricResidue

open Polynomial Finset
open scoped BigOperators

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
  {s : Finset ι} {v : ι → K} {i : ι}

noncomputable def cofactor (s : Finset ι) (v : ι → K) (i : ι) : K[X] :=
  Lagrange.nodal (s.erase i) v

theorem cofactor_value_ne_zero (hv : Set.InjOn v s) (hi : i ∈ s) :
    (cofactor s v i).eval (v i) ≠ 0 := by
  apply Lagrange.eval_nodal_not_at_node
  intro j hj he
  exact (mem_erase.mp hj).1 (hv (mem_erase.mp hj).2 hi he.symm)

theorem basis_eq_weight_cofactor (hi : i ∈ s) :
    Lagrange.basis s v i = C (Lagrange.nodalWeight s v i) * cofactor s v i := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
    ← Lagrange.nodal_erase_eq_nodal_div hi]
  rfl

theorem basis_linear_relation (hi : i ∈ s) :
    (X - C (v i)) * Lagrange.basis s v i =
      C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [basis_eq_weight_cofactor hi, Lagrange.nodal_eq_mul_nodal_erase hi]
  unfold cofactor
  ring

theorem derivative_linear_product_eval (p : K[X]) (a : K) :
    (derivative ((X - C a) * p)).eval a = p.eval a := by
  simp [derivative_mul]

theorem second_derivative_linear_product_eval (p : K[X]) (a : K) :
    (derivative (derivative ((X - C a) * p))).eval a =
      2 * (derivative p).eval a := by
  simp [derivative_mul]
  ring

theorem derivative_basis_sum (hv : Set.InjOn v s) (hi : i ∈ s) :
    (∑ j ∈ s, (derivative (Lagrange.basis s v j)).eval (v i)) = 0 := by
  have h := congrArg (fun p : K[X] => (derivative p).eval (v i))
    (Lagrange.sum_basis hv ⟨i, hi⟩)
  simpa only [derivative_sum, eval_finsetSum, derivative_one, eval_zero] using h

theorem second_derivative_basis_sum (hv : Set.InjOn v s) (hi : i ∈ s) :
    (∑ j ∈ s, (derivative (derivative (Lagrange.basis s v j))).eval (v i)) = 0 := by
  have h := congrArg (fun p : K[X] => (derivative (derivative p)).eval (v i))
    (Lagrange.sum_basis hv ⟨i, hi⟩)
  simpa only [derivative_sum, eval_finsetSum, derivative_one, derivative_zero, eval_zero] using h

theorem basis_derivative_at_other (hv : Set.InjOn v s) (hi : i ∈ s)
    {j : ι} (hj : j ∈ s.erase i) :
    (derivative (Lagrange.basis s v j)).eval (v i) =
      (cofactor s v i).eval (v i) *
        (Lagrange.nodalWeight s v j / (v i - v j)) := by
  have hji : j ≠ i := (mem_erase.mp hj).1
  have hjs : j ∈ s := (mem_erase.mp hj).2
  have hd : v i - v j ≠ 0 := sub_ne_zero.mpr (fun h => hji (hv hjs hi h.symm))
  have h := congrArg (fun p : K[X] => (derivative p).eval (v i))
    (basis_linear_relation (v := v) hjs)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    Lagrange.eval_basis_of_ne hji hi, zero_mul, zero_add,
    Lagrange.eval_nodal_derivative_eval_node_eq hi] at h
  change (v i - v j) * (derivative (Lagrange.basis s v j)).eval (v i) =
    Lagrange.nodalWeight s v j * (cofactor s v i).eval (v i) at h
  apply (mul_left_cancel₀ hd)
  calc
    (v i - v j) * (derivative (Lagrange.basis s v j)).eval (v i) =
        Lagrange.nodalWeight s v j * (cofactor s v i).eval (v i) := h
    _ = (v i - v j) * ((cofactor s v i).eval (v i) *
        (Lagrange.nodalWeight s v j / (v i - v j))) := by field_simp

theorem basis_derivative_at_self (hi : i ∈ s) :
    (derivative (Lagrange.basis s v i)).eval (v i) =
      ((cofactor s v i).eval (v i))⁻¹ * (derivative (cofactor s v i)).eval (v i) := by
  rw [basis_eq_weight_cofactor hi]
  simp [Lagrange.nodalWeight_eq_eval_nodal_erase_inv, cofactor]

theorem basis_second_derivative_at_self (hi : i ∈ s) :
    (derivative (derivative (Lagrange.basis s v i))).eval (v i) =
      ((cofactor s v i).eval (v i))⁻¹ *
        (derivative (derivative (cofactor s v i))).eval (v i) := by
  rw [basis_eq_weight_cofactor hi]
  simp [Lagrange.nodalWeight_eq_eval_nodal_erase_inv, cofactor]

theorem second_derivative_linear_product_eval_at (p : K[X]) (a b : K) :
    (derivative (derivative ((X - C b) * p))).eval a =
      2 * (derivative p).eval a + (a - b) * (derivative (derivative p)).eval a := by
  simp [derivative_mul]
  ring

theorem basis_second_derivative_at_other (hv : Set.InjOn v s) (hi : i ∈ s)
    {j : ι} (hj : j ∈ s.erase i) :
    (derivative (derivative (Lagrange.basis s v j))).eval (v i) =
      2 * Lagrange.nodalWeight s v j *
        ((derivative (cofactor s v i)).eval (v i) / (v i - v j) -
          (cofactor s v i).eval (v i) / (v i - v j) ^ 2) := by
  have hji : j ≠ i := (mem_erase.mp hj).1
  have hjs : j ∈ s := (mem_erase.mp hj).2
  have hd : v i - v j ≠ 0 := sub_ne_zero.mpr (fun h => hji (hv hjs hi h.symm))
  have hn : (derivative (derivative (Lagrange.nodal s v))).eval (v i) =
      2 * (derivative (cofactor s v i)).eval (v i) := by
    rw [Lagrange.nodal_eq_mul_nodal_erase hi]
    exact second_derivative_linear_product_eval _ _
  have h := congrArg (fun p : K[X] => (derivative (derivative p)).eval (v i))
    (basis_linear_relation (v := v) hjs)
  rw [second_derivative_linear_product_eval_at] at h
  simp only [derivative_C_mul, eval_mul, eval_C, hn] at h
  rw [basis_derivative_at_other hv hi hj] at h
  apply (mul_left_cancel₀ hd)
  field_simp at h ⊢
  linear_combination h

theorem weighted_reciprocal_sum (hv : Set.InjOn v s) (hi : i ∈ s) :
    (cofactor s v i).eval (v i) ^ 2 *
      (∑ j ∈ s.erase i, Lagrange.nodalWeight s v j / (v i - v j)) =
        -(derivative (cofactor s v i)).eval (v i) := by
  have hD := cofactor_value_ne_zero hv hi
  have hs := derivative_basis_sum hv hi
  rw [← sum_erase_add _ _ hi, basis_derivative_at_self hi] at hs
  have he : (∑ j ∈ s.erase i, (derivative (Lagrange.basis s v j)).eval (v i)) =
      (cofactor s v i).eval (v i) *
        (∑ j ∈ s.erase i, Lagrange.nodalWeight s v j / (v i - v j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    exact basis_derivative_at_other hv hi hj
  rw [he] at hs
  field_simp [hD] at hs
  linear_combination hs

theorem weighted_reciprocal_square_sum (hv : Set.InjOn v s) (hi : i ∈ s) :
    2 * (cofactor s v i).eval (v i) ^ 3 *
      (∑ j ∈ s.erase i, Lagrange.nodalWeight s v j / (v i - v j) ^ 2) =
        (cofactor s v i).eval (v i) *
          (derivative (derivative (cofactor s v i))).eval (v i) -
        2 * (derivative (cofactor s v i)).eval (v i) ^ 2 := by
  have hD := cofactor_value_ne_zero hv hi
  have hs := second_derivative_basis_sum hv hi
  rw [← sum_erase_add _ _ hi, basis_second_derivative_at_self hi] at hs
  have he : (∑ j ∈ s.erase i,
      (derivative (derivative (Lagrange.basis s v j))).eval (v i)) =
      2 * (derivative (cofactor s v i)).eval (v i) *
        (∑ j ∈ s.erase i, Lagrange.nodalWeight s v j / (v i - v j)) -
      2 * (cofactor s v i).eval (v i) *
        (∑ j ∈ s.erase i, Lagrange.nodalWeight s v j / (v i - v j) ^ 2) := by
    calc
      _ = ∑ j ∈ s.erase i,
          (2 * (derivative (cofactor s v i)).eval (v i) *
              (Lagrange.nodalWeight s v j / (v i - v j)) -
            2 * (cofactor s v i).eval (v i) *
              (Lagrange.nodalWeight s v j / (v i - v j) ^ 2)) := by
        apply sum_congr rfl
        intro j hj
        rw [basis_second_derivative_at_other hv hi hj]
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
  rw [he] at hs
  have hfirst := weighted_reciprocal_sum hv hi
  field_simp [hD] at hs
  linear_combination -(cofactor s v i).eval (v i) * hs +
    2 * (derivative (cofactor s v i)).eval (v i) * hfirst

theorem nodal_derivative_eval (x : K) (hx : ∀ j ∈ s, x ≠ v j) :
    (derivative (Lagrange.nodal s v)).eval x =
      (Lagrange.nodal s v).eval x * (∑ j ∈ s, 1 / (x - v j)) := by
  rw [Lagrange.derivative_nodal, eval_finsetSum, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [Lagrange.nodal_eq_mul_nodal_erase hj, eval_mul, eval_sub, eval_X, eval_C]
  have hd := sub_ne_zero.mpr (hx j hj)
  field_simp

theorem nodal_second_derivative_eval (x : K) (hx : ∀ j ∈ s, x ≠ v j) :
    (derivative (derivative (Lagrange.nodal s v))).eval x =
      (Lagrange.nodal s v).eval x *
        ((∑ j ∈ s, 1 / (x - v j)) ^ 2 - ∑ j ∈ s, (1 / (x - v j)) ^ 2) := by
  let S : K := ∑ j ∈ s, 1 / (x - v j)
  let D : K := (Lagrange.nodal s v).eval x
  have ht {j : ι} (hj : j ∈ s) :
      (derivative (Lagrange.nodal (s.erase j) v)).eval x =
        D * ((1 / (x - v j)) * S - (1 / (x - v j)) ^ 2) := by
    rw [nodal_derivative_eval x (fun k hk => hx k (mem_of_mem_erase hk))]
    have hs : (∑ k ∈ s.erase j, 1 / (x - v k)) = S - 1 / (x - v j) := by
      exact eq_sub_iff_add_eq.mpr (sum_erase_add _ _ hj)
    rw [hs]
    have hD : D = (x - v j) * (Lagrange.nodal (s.erase j) v).eval x := by
      dsimp [D]
      rw [Lagrange.nodal_eq_mul_nodal_erase hj]
      simp
    rw [hD]
    have hd := sub_ne_zero.mpr (hx j hj)
    field_simp
  rw [Lagrange.derivative_nodal, derivative_sum, eval_finsetSum]
  change _ = D * (S ^ 2 - _)
  calc
    _ = ∑ j ∈ s, D * ((1 / (x - v j)) * S - (1 / (x - v j)) ^ 2) :=
      sum_congr rfl (fun j hj => ht hj)
    _ = D * (S ^ 2 - ∑ j ∈ s, (1 / (x - v j)) ^ 2) := by
      rw [← mul_sum, sum_sub_distrib, ← sum_mul]
      dsimp [S]
      ring

/-- The regular second coefficient of the barycentric partial fraction sum,
    expressed only through reciprocal differences of distinct nodes. -/
theorem finite_residue_identity (hv : Set.InjOn v s) (hi : i ∈ s) :
    2 * (cofactor s v i).eval (v i) *
      (∑ j ∈ s.erase i, Lagrange.nodalWeight s v j / (v i - v j) ^ 2) =
      -((∑ j ∈ s.erase i, 1 / (v i - v j)) ^ 2 +
        ∑ j ∈ s.erase i, (1 / (v i - v j)) ^ 2) := by
  have hx : ∀ j ∈ s.erase i, v i ≠ v j := by
    intro j hj h
    exact (mem_erase.mp hj).1 (hv (mem_of_mem_erase hj) hi h.symm)
  have h := weighted_reciprocal_square_sum hv hi
  have hfirst := nodal_derivative_eval (v i) hx
  have hsecond := nodal_second_derivative_eval (v i) hx
  change (derivative (cofactor s v i)).eval (v i) = _ at hfirst
  change (derivative (derivative (cofactor s v i))).eval (v i) = _ at hsecond
  rw [hfirst, hsecond] at h
  have hD := pow_ne_zero 2 (cofactor_value_ne_zero hv hi)
  apply (mul_left_cancel₀ hD)
  unfold cofactor at h ⊢
  linear_combination h

#print axioms cofactor_value_ne_zero
#print axioms basis_derivative_at_other
#print axioms weighted_reciprocal_sum
#print axioms weighted_reciprocal_square_sum
#print axioms nodal_derivative_eval
#print axioms nodal_second_derivative_eval
#print axioms finite_residue_identity

end TRR08Geometry.BarycentricResidue
