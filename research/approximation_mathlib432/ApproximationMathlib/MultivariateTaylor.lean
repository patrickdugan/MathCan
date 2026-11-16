import ApproximationMathlib.CapturedApproximation

/-! Genuine multivariate Taylor coefficients, synthesized from the coordinate
components of Frechet derivative tensors. Grouping by exponent counts avoids
assuming a mixed-partial or Taylor-remainder oracle. -/
namespace MathCan.MultivariateTaylor
open Set MathCan.TaylorFoundation
open scoped Nat
set_option autoImplicit false

abbrev Space (d : ℕ) := Fin d → ℝ
noncomputable def basis {d : ℕ} (j : Fin d) : Space d := Pi.single j 1

theorem sum_basis {d : ℕ} (h : Space d) : (∑j,h j • basis j)=h := by
  classical
  ext i
  simp [basis,Finset.sum_apply,Pi.single_apply]

theorem basis_bound {d : ℕ} (j : Fin d) : ‖basis j‖≤1 := by
  classical
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro i
  by_cases hi:i=j <;> simp [basis,Pi.single_apply,hi]

noncomputable def lineMap {d : ℕ} (h : Space d) : ℝ →L[ℝ] Space d :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight h

noncomputable def along {d : ℕ} (f : Space d → ℝ) (a h : Space d) (t : ℝ) : ℝ :=
  f (a+t • h)

theorem along_contDiff {d k : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f) (a h : Space d) :
    ContDiff ℝ k (along f a h) := by
  unfold along
  exact hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem along_iteratedDeriv {d k n : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f)
    (hn : n≤k) (a h : Space d) (t : ℝ) :
    iteratedDeriv n (along f a h) t=iteratedFDeriv ℝ n f (a+t • h) (fun _=>h) := by
  have hg:ContDiff ℝ k (fun z:Space d=>f (a+z)):=hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ n ((fun z:Space d=>f (a+z)) ∘ lineMap h) t (fun _=>1)=_
  rw [(lineMap h).iteratedFDeriv_comp_right hg t (by exact_mod_cast hn)]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,lineMap,iteratedFDeriv_comp_add_left]

noncomputable def tensorPolynomial {d : ℕ} (f : Space d → ℝ) (k : ℕ) (a h : Space d) : ℝ :=
  ∑n∈Finset.range (k+1),(Nat.factorial n:ℝ)⁻¹*iteratedFDeriv ℝ n f a (fun _=>h)

theorem line_taylor_eq_tensor {d k : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f) (a h : Space d) :
    taylorWithinEval (along f a h) k (uIcc (0:ℝ) 1) 0 1=tensorPolynomial f k a h := by
  rw [taylor_within_apply]
  unfold tensorPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnk:n≤k:=by have:=Finset.mem_range.mp hn; omega
  have hs:UniqueDiffOn ℝ (uIcc (0:ℝ) 1):=uniqueDiffOn_Icc (by norm_num)
  rw [iteratedDerivWithin_eq_iteratedDeriv hs ((along_contDiff hf a h).of_le (by exact_mod_cast hnk)).contDiffAt left_mem_uIcc,
    along_iteratedDeriv hf hnk a h 0]
  simp

theorem tensor_expansion {d n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n=>Space d) ℝ) (h : Space d) :
    T (fun _=>h)=∑w:Fin n→Fin d,(∏r,h (w r))*T (fun r=>basis (w r)) := by
  classical
  have he:(fun _ : Fin n=>h)=(fun _=>∑j,h j • basis j) := by funext r; exact (sum_basis h).symm
  rw [he]
  change T.toMultilinearMap (fun _=>∑j,h j • basis j)=_
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [MultilinearMap.map_smul_univ]
  rfl

def counts {d n : ℕ} (w : Fin n → Fin d) (j : Fin d) : ℕ :=
  (Finset.univ.filter (fun r=>w r=j)).card

theorem counts_le {d n : ℕ} (w : Fin n → Fin d) (j : Fin d) : counts w j≤n := by
  unfold counts
  exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)

noncomputable def monomial {d : ℕ} (beta : Fin d → ℕ) (h : Space d) : ℝ := ∏j,h j^(beta j)

theorem word_monomial {d n : ℕ} (w : Fin n → Fin d) (h : Space d) :
    (∏r,h (w r))=monomial (counts w) h := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ w (fun r=>h (w r))]
  unfold monomial counts
  apply Finset.prod_congr rfl
  intro j _
  calc
    _ = ∏r∈Finset.univ.filter (fun r=>w r=j),h j := by
      apply Finset.prod_congr rfl
      intro r hr
      rw [(Finset.mem_filter.mp hr).2]
    _ = _ := by simp

abbrev Index (d k : ℕ) := Fin d → Fin (k+1)
abbrev size (d k : ℕ) := Fintype.card (Index d k)
noncomputable def labels (d k : ℕ) (j : Fin (size d k)) : Fin d → ℕ :=
  fun axis=>((Fintype.equivFin (Index d k)).symm j axis).val

theorem labels_injective (d k : ℕ) : Function.Injective (labels d k) := by
  intro j l he
  apply (Fintype.equivFin (Index d k)).symm.injective
  funext axis
  apply Fin.ext
  exact congrFun he axis

theorem labels_degree (d k : ℕ) (j : Fin (size d k)) (axis : Fin d) : labels d k j axis≤k :=
  Nat.le_of_lt_succ ((Fintype.equivFin (Index d k)).symm j axis).isLt

noncomputable def wordIndex {d k n : ℕ} (w : Fin n → Fin d) (hn : n≤k) : Fin (size d k) :=
  Fintype.equivFin (Index d k) (fun j=>⟨counts w j,by have:=counts_le w j; omega⟩)

theorem wordIndex_labels {d k n : ℕ} (w : Fin n → Fin d) (hn : n≤k) :
    labels d k (wordIndex w hn)=counts w := by
  funext axis
  simp [labels,wordIndex]

noncomputable def coefficients {d : ℕ} (f : Space d → ℝ) (k : ℕ) (a : Space d) :
    Fin (size d k) → ℝ := fun j=>
  ∑n∈Finset.range (k+1),∑w:Fin n→Fin d,
    if counts w=labels d k j then (Nat.factorial n:ℝ)⁻¹*iteratedFDeriv ℝ n f a (fun r=>basis (w r)) else 0

noncomputable def evaluate {d k : ℕ} (q : Fin (size d k) → ℝ) (h : Space d) : ℝ :=
  ∑j,q j*monomial (labels d k j) h

theorem evaluate_coefficients {d k : ℕ} (f : Space d → ℝ) (a h : Space d) :
    evaluate (coefficients f k a) h=tensorPolynomial f k a h := by
  classical
  unfold evaluate coefficients tensorPolynomial
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm,tensor_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have hnk:n≤k:=by have:=Finset.mem_range.mp hn; omega
  rw [Finset.sum_eq_single (wordIndex w hnk)]
  · rw [if_pos (wordIndex_labels w hnk).symm,wordIndex_labels,← word_monomial]
    ring
  · intro j _ hne
    have hh:counts w≠labels d k j := by
      intro he
      exact hne (labels_injective d k (he.symm.trans (wordIndex_labels w hnk).symm))
    simp [hh]
  · simp

end MathCan.MultivariateTaylor
