module

public import TRR08Geometry.PolynomialDegree
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Ordinary-degree representatives of weighted short-curve normal forms

On `y² = x³ + A*x + B`, the bivariate polynomial `Y²-A*X-B` evaluates
to `x³` and has ordinary total degree at most two. Expanding an exponent
modulo three therefore constructs representatives of `x^j` and `y*x^j`
with the required ordinary degree. Finite coefficient sums give explicit
representatives of every normal form `p(x)+y*q(x)`.
-/

@[expose] public section

namespace TRR08Geometry

open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def cubicLiftBase (A B : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 1 ^ 2 - MvPolynomial.C A * MvPolynomial.X 0 - MvPolynomial.C B

noncomputable def monomialLift (A B : K) (j : ℕ) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ (j % 3) * cubicLiftBase A B ^ (j / 3)

noncomputable def oddMonomialLift (A B : K) (j : ℕ) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 1 * monomialLift A B j

theorem cubicLiftBase_eval (A B x y : K) (hy : y ^ 2 = x ^ 3 + A * x + B) :
    bivariateEval (cubicLiftBase A B) x y = x ^ 3 := by
  simp only [bivariateEval, cubicLiftBase, map_sub, map_pow, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hy]
  ring

theorem cubicLiftBase_totalDegree (A B : K) :
    (cubicLiftBase A B).totalDegree ≤ 2 := by
  unfold cubicLiftBase
  apply (MvPolynomial.totalDegree_sub_C_le _ _).trans
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp

theorem monomialLift_eval (A B x y : K) (hy : y ^ 2 = x ^ 3 + A * x + B)
    (j : ℕ) : bivariateEval (monomialLift A B j) x y = x ^ j := by
  change MvPolynomial.eval ![x, y] (_ * _) = _
  rw [map_mul, map_pow, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero]
  change x ^ (j % 3) * (bivariateEval (cubicLiftBase A B) x y) ^ (j / 3) = _
  rw [cubicLiftBase_eval A B x y hy, ← pow_mul, ← pow_add, Nat.mod_add_div]

theorem monomialLift_totalDegree_bound (A B : K) (j : ℕ) :
    (monomialLift A B j).totalDegree ≤ 2 * (j / 3) + j % 3 := by
  unfold monomialLift
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hp := (MvPolynomial.totalDegree_pow (cubicLiftBase A B) (j / 3)).trans
    (Nat.mul_le_mul_left (j / 3) (cubicLiftBase_totalDegree A B))
  simpa only [MvPolynomial.totalDegree_X_pow, Nat.mul_comm, Nat.add_comm] using
    Nat.add_le_add_left hp (j % 3)

/-- A weighted even monomial has an ordinary-degree representative. -/
theorem monomialLift_totalDegree_le (A B : K) {j d : ℕ} (h : 2 * j ≤ 3 * d) :
    (monomialLift A B j).totalDegree ≤ d := by
  apply (monomialLift_totalDegree_bound A B j).trans
  have hm := Nat.mod_lt j (by decide : 0 < 3)
  have he := Nat.mod_add_div j 3
  omega

theorem oddMonomialLift_eval (A B x y : K) (hy : y ^ 2 = x ^ 3 + A * x + B)
    (j : ℕ) : bivariateEval (oddMonomialLift A B j) x y = y * x ^ j := by
  change MvPolynomial.eval ![x, y] (_ * _) = _
  rw [map_mul, MvPolynomial.eval_X, Matrix.cons_val_one]
  exact congrArg (y * ·) (monomialLift_eval A B x y hy j)

/-- A weighted odd monomial has an ordinary-degree representative. -/
theorem oddMonomialLift_totalDegree_le (A B : K) {j d : ℕ}
    (h : 2 * j + 3 ≤ 3 * d) :
    (oddMonomialLift A B j).totalDegree ≤ d := by
  unfold oddMonomialLift
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hm := Nat.mod_lt j (by decide : 0 < 3)
  have he := Nat.mod_add_div j 3
  have hj := monomialLift_totalDegree_bound A B j
  rw [MvPolynomial.totalDegree_X]
  omega

noncomputable def polynomialLift (A B : K) (p : Polynomial K) :
    MvPolynomial (Fin 2) K :=
  ∑ j ∈ p.support, MvPolynomial.C (p.coeff j) * monomialLift A B j

noncomputable def oddPolynomialLift (A B : K) (q : Polynomial K) :
    MvPolynomial (Fin 2) K :=
  ∑ j ∈ q.support, MvPolynomial.C (q.coeff j) * oddMonomialLift A B j

theorem polynomialLift_eval (A B x y : K) (hy : y ^ 2 = x ^ 3 + A * x + B)
    (p : Polynomial K) : bivariateEval (polynomialLift A B p) x y = p.eval x := by
  unfold polynomialLift bivariateEval
  rw [map_sum]
  simp only [map_mul, MvPolynomial.eval_C]
  change (∑ j ∈ p.support, p.coeff j * bivariateEval (monomialLift A B j) x y) = _
  simp_rw [monomialLift_eval A B x y hy]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]

theorem oddPolynomialLift_eval (A B x y : K) (hy : y ^ 2 = x ^ 3 + A * x + B)
    (q : Polynomial K) : bivariateEval (oddPolynomialLift A B q) x y = y * q.eval x := by
  unfold oddPolynomialLift bivariateEval
  rw [map_sum]
  simp only [map_mul, MvPolynomial.eval_C]
  change (∑ j ∈ q.support, q.coeff j * bivariateEval (oddMonomialLift A B j) x y) = _
  simp_rw [oddMonomialLift_eval A B x y hy]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem polynomialLift_totalDegree_le (A B : K) (p : Polynomial K) {d : ℕ}
    (hp : 2 * p.natDegree ≤ 3 * d) : (polynomialLift A B p).totalDegree ≤ d := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  have hle := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact monomialLift_totalDegree_le A B (by omega)

theorem oddPolynomialLift_totalDegree_le (A B : K) (q : Polynomial K) {d : ℕ}
    (hq : 2 * q.natDegree + 3 ≤ 3 * d) : (oddPolynomialLift A B q).totalDegree ≤ d := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  have hle := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact oddMonomialLift_totalDegree_le A B (by omega)

noncomputable def normalFormLift (A B : K) (p q : Polynomial K) :
    MvPolynomial (Fin 2) K := polynomialLift A B p + oddPolynomialLift A B q

theorem normalFormLift_eval (A B x y : K) (hy : y ^ 2 = x ^ 3 + A * x + B)
    (p q : Polynomial K) :
    bivariateEval (normalFormLift A B p q) x y = p.eval x + y * q.eval x := by
  change MvPolynomial.eval ![x, y] (_ + _) = _
  rw [map_add]
  exact congrArg₂ (· + ·) (polynomialLift_eval A B x y hy p)
    (oddPolynomialLift_eval A B x y hy q)

/-- Every weighted normal form under weight `3*d` has an actual bivariate lift. -/
theorem normalFormLift_totalDegree_le (A B : K) (p q : Polynomial K) {d : ℕ}
    (hp : 2 * p.natDegree ≤ 3 * d) (hq : 2 * q.natDegree + 3 ≤ 3 * d) :
    (normalFormLift A B p q).totalDegree ≤ d := by
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le (polynomialLift_totalDegree_le A B p hp)
      (oddPolynomialLift_totalDegree_le A B q hq))

end TRR08Geometry

#print axioms TRR08Geometry.cubicLiftBase_eval
#print axioms TRR08Geometry.cubicLiftBase_totalDegree
#print axioms TRR08Geometry.monomialLift_eval
#print axioms TRR08Geometry.monomialLift_totalDegree_le
#print axioms TRR08Geometry.oddMonomialLift_eval
#print axioms TRR08Geometry.oddMonomialLift_totalDegree_le
#print axioms TRR08Geometry.polynomialLift_eval
#print axioms TRR08Geometry.oddPolynomialLift_eval
#print axioms TRR08Geometry.polynomialLift_totalDegree_le
#print axioms TRR08Geometry.oddPolynomialLift_totalDegree_le
#print axioms TRR08Geometry.normalFormLift_eval
#print axioms TRR08Geometry.normalFormLift_totalDegree_le
