module

public import TRR08Geometry.BlockPolynomial
public import TRR08Geometry.PolynomialDegree

/-!
# Building an actual block polynomial from bivariate interpolants

The tensor polynomial is an explicit finite sum of four-variable monomials.
Its support records ordinary coordinate-pair bounds directly. Interpolating
point masses in each pair then constructs a polynomial for any finite matrix.
-/

@[expose] public section

namespace TRR08Geometry

open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def blockExponent (a b : Fin 2 →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a 0, a 1, b 0, b 1]

theorem BlockDegreeLE_monomial {d : ℕ} (e : Fin 4 →₀ ℕ) (c : K)
    (h₁ : e 0 + e 1 ≤ d) (h₂ : e 2 + e 3 ≤ d) :
    BlockDegreeLE d (MvPolynomial.monomial e c) := by
  intro f hf
  have he : f = e := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hf)
  simpa only [he] using And.intro h₁ h₂

theorem BlockDegreeLE_sum {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin 4) K) {d : ℕ}
    (hF : ∀ i ∈ s, BlockDegreeLE d (F i)) :
    BlockDegreeLE d (∑ i ∈ s, F i) := by
  classical
  intro e he
  rcases Finset.mem_biUnion.mp (MvPolynomial.support_sum he) with ⟨i, hi, hei⟩
  exact hF i hi e hei

theorem BlockDegreeLE_smul {d : ℕ} {D : MvPolynomial (Fin 4) K}
    (hD : BlockDegreeLE d D) (c : K) : BlockDegreeLE d (c • D) := by
  intro e he
  exact hD e (MvPolynomial.support_smul he)

theorem blockEval_sum {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin 4) K) (x₁ y₁ x₂ y₂ : K) :
    blockEval (∑ i ∈ s, F i) x₁ y₁ x₂ y₂ =
      ∑ i ∈ s, blockEval (F i) x₁ y₁ x₂ y₂ := by
  simp [blockEval]

theorem blockEval_smul (c : K) (D : MvPolynomial (Fin 4) K) (x₁ y₁ x₂ y₂ : K) :
    blockEval (c • D) x₁ y₁ x₂ y₂ = c * blockEval D x₁ y₁ x₂ y₂ := by
  simp [blockEval]

theorem blockEval_tensor_monomial (a b : Fin 2 →₀ ℕ) (c : K) (x₁ y₁ x₂ y₂ : K) :
    blockEval (MvPolynomial.monomial (blockExponent a b) c) x₁ y₁ x₂ y₂ =
      c * (x₁ ^ a 0 * y₁ ^ a 1) * (x₂ ^ b 0 * y₂ ^ b 1) := by
  simp only [blockEval, MvPolynomial.eval_monomial]
  simp [Fin.prod_univ_four, blockExponent, mul_assoc]

noncomputable def blockTensor (F G : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 4) K :=
  ∑ a ∈ F.support, ∑ b ∈ G.support,
    MvPolynomial.monomial (blockExponent a b) (F.coeff a * G.coeff b)

theorem blockTensor_degree {d : ℕ} (F G : MvPolynomial (Fin 2) K)
    (hF : F.totalDegree ≤ d) (hG : G.totalDegree ≤ d) :
    BlockDegreeLE d (blockTensor F G) := by
  apply BlockDegreeLE_sum
  intro a ha
  apply BlockDegreeLE_sum
  intro b hb
  apply BlockDegreeLE_monomial
  · simpa [blockExponent] using (bivariate_support_totalDegree F ha).trans hF
  · simpa [blockExponent] using (bivariate_support_totalDegree G hb).trans hG

theorem blockTensor_eval (F G : MvPolynomial (Fin 2) K) (x₁ y₁ x₂ y₂ : K) :
    blockEval (blockTensor F G) x₁ y₁ x₂ y₂ =
      bivariateEval F x₁ y₁ * bivariateEval G x₂ y₂ := by
  unfold blockTensor
  simp_rw [blockEval_sum, blockEval_tensor_monomial, bivariateEval_eq_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

noncomputable def matrixPolynomial {ι : Type*} [Fintype ι]
    (M : ι → ι → K) (F : ι → MvPolynomial (Fin 2) K) : MvPolynomial (Fin 4) K :=
  ∑ P : ι, ∑ Q : ι, M P Q • blockTensor (F P) (F Q)

theorem matrixPolynomial_degree {ι : Type*} [Fintype ι]
    (M : ι → ι → K) (F : ι → MvPolynomial (Fin 2) K) {d : ℕ}
    (hF : ∀ P, (F P).totalDegree ≤ d) :
    BlockDegreeLE d (matrixPolynomial M F) := by
  apply BlockDegreeLE_sum
  intro P _
  apply BlockDegreeLE_sum
  intro Q _
  exact BlockDegreeLE_smul (blockTensor_degree (F P) (F Q) (hF P) (hF Q)) (M P Q)

/-- Point-mass interpolants construct every finite matrix with the same block bound. -/
theorem matrixPolynomial_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → K) (F : ι → MvPolynomial (Fin 2) K) (x y : ι → K)
    (hF : ∀ P Q, bivariateEval (F P) (x Q) (y Q) = if Q = P then 1 else 0)
    (P Q : ι) : blockEval (matrixPolynomial M F) (x P) (y P) (x Q) (y Q) = M P Q := by
  unfold matrixPolynomial
  simp_rw [blockEval_sum, blockEval_smul, blockTensor_eval, hF]
  simp [mul_ite]

end TRR08Geometry

#print axioms TRR08Geometry.BlockDegreeLE_monomial
#print axioms TRR08Geometry.BlockDegreeLE_sum
#print axioms TRR08Geometry.BlockDegreeLE_smul
#print axioms TRR08Geometry.blockEval_tensor_monomial
#print axioms TRR08Geometry.blockTensor_degree
#print axioms TRR08Geometry.blockTensor_eval
#print axioms TRR08Geometry.matrixPolynomial_degree
#print axioms TRR08Geometry.matrixPolynomial_eval
