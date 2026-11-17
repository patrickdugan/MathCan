import ApproximationMathlib.SharpTransport

/-! Ordered derivative words give a normalized multivariate jet with an exact
integer transport matrix. Directional order is retained in the registers. -/
namespace MathCan.WordTransport
open MathCan.MultivariateTaylor MathCan.MultivariateBounds MathCan.SharpResidual
open Set
open scoped Nat
set_option autoImplicit false

noncomputable def directional {d : ℕ} : List (Fin d) → (Space d → ℝ) → Space d → ℝ
  | [],f => f
  | j::w,f => fun x=>fderiv ℝ (directional w f) x (basis j)

theorem directional_append {d : ℕ} (u w : List (Fin d)) (f : Space d → ℝ) :
    directional (u++w) f=directional u (directional w f) := by
  induction u with
  | nil => rfl
  | cons j u ih => simp only [List.cons_append,directional,ih]

theorem basis_cons {d : ℕ} (j : Fin d) (w : List (Fin d)) :
    (fun i : Fin (j::w).length=>basis ((j::w).get i))=
      Fin.cons (basis j) (fun i=>basis (w.get i)) := by
  funext i
  cases i using Fin.cases <;> simp [Fin.cons]

theorem directional_component {d k : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f)
    (w : List (Fin d)) (hw : w.length≤k) (x : Space d) :
    directional w f x=iteratedFDeriv ℝ w.length f x (fun i=>basis (w.get i)) := by
  induction w generalizing x with
  | nil => simp [directional]
  | cons j w ih =>
    have he : directional w f=(fun y=>iteratedFDeriv ℝ w.length f y (fun i=>basis (w.get i))) :=
      funext (fun y=>ih (by simp only [List.length_cons] at hw; omega) y)
    have hd : ContDiff ℝ 1 (iteratedFDeriv ℝ w.length f) :=
      hf.iteratedFDeriv_right (by exact_mod_cast (show 1+w.length≤k by simp only [List.length_cons] at hw; omega))
    simp only [directional,he,List.length_cons]
    rw [fderiv_continuousMultilinear_apply_const_apply (hd.differentiable (by norm_num)).differentiableAt]
    rfl

theorem directional_contDiff {d m : ℕ} {f : Space d → ℝ} (w : List (Fin d))
    (hf : ContDiff ℝ (m+w.length:ℕ) f) : ContDiff ℝ m (directional w f) := by
  have he : directional w f=component f w.get := funext (directional_component hf w (by omega))
  rw [he]
  exact component_contDiff (by simpa only [Nat.cast_add] using hf) w.get

theorem directional_ofFn {d r k : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f)
    (w : Fin r → Fin d) (hr : r≤k) (x : Space d) :
    directional (List.ofFn w) f x=iteratedFDeriv ℝ r f x (fun i=>basis (w i)) := by
  induction r generalizing x with
  | zero => simp [directional]
  | succ r ih =>
    have he : directional (List.ofFn (fun i:Fin r=>w i.succ)) f=
        (fun y=>iteratedFDeriv ℝ r f y (fun i=>basis (w i.succ))) :=
      funext (fun y=>ih _ (by omega) y)
    have hd : ContDiff ℝ 1 (iteratedFDeriv ℝ r f) :=
      hf.iteratedFDeriv_right (by exact_mod_cast (show 1+r≤k by omega))
    rw [List.ofFn_succ]
    simp only [directional,he]
    rw [fderiv_continuousMultilinear_apply_const_apply (hd.differentiable (by norm_num)).differentiableAt]
    rfl

theorem repeated_component {d m k : ℕ} {g : Space d → ℝ} (hg : ContDiff ℝ k g)
    (hm : m≤k) (axis : Fin d) (x : Space d) :
    iteratedFDeriv ℝ m g x (fun _=>basis axis)=directional (List.replicate m axis) g x := by
  simpa using (directional_ofFn hg (fun _:Fin m=>axis) hm x).symm

theorem tensor_scale {d n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n=>Space d) ℝ)
    (z : ℝ) (b : Space d) : T (fun _=>z • b)=z^n*T (fun _=>b) := by
  change T.toMultilinearMap (fun _=>z • b)=_
  rw [MultilinearMap.map_smul_univ]
  simp

noncomputable def jet {d : ℕ} (mu : ℝ) (f : Space d → ℝ) (a : Space d) (w : List (Fin d)) : ℝ :=
  scaledValue mu w.length (directional w f) a

theorem factorial_transport (r t : ℕ) (mu q z : ℝ) :
    (mu^r/((Nat.factorial r):ℝ))*(((Nat.factorial t):ℝ)⁻¹*((mu*q)^t*z))=
      ((t+r).choose r:ℝ)*q^t*(mu^(t+r)/((t+r)!:ℝ)*z) := by
  have he : ((t+r).choose r:ℝ)*((Nat.factorial r):ℝ)*((Nat.factorial t):ℝ)=((t+r)!:ℝ) := by
    exact_mod_cast (show (t+r).choose r*(Nat.factorial r)*(Nat.factorial t)=(t+r)! by
      simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.add_choose_mul_factorial_mul_factorial t r)
  have hr : ((Nat.factorial r):ℝ)≠0 := by positivity
  have ht : ((Nat.factorial t):ℝ)≠0 := by positivity
  have hrt : ((t+r)!:ℝ)≠0 := by positivity
  rw [pow_add,mul_pow]
  field_simp
  rw [← he]
  ring

/-- Exact compatibility, with no matrix or residual identity premise. -/
theorem row_compatibility {d m : ℕ} {f : Space d → ℝ} (w : List (Fin d))
    (hf : ContDiff ℝ (m+w.length:ℕ) f) (a : Space d) (axis : Fin d) (mu q : ℝ) :
    scaledTaylor mu w.length m (directional w f) a ((mu*q) • basis axis)=
      ∑t∈Finset.range (m+1),((t+w.length).choose w.length:ℝ)*q^t*
        jet mu f a (List.replicate t axis++w) := by
  have hg:=directional_contDiff w hf
  unfold scaledTaylor tensorPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htm : t≤m := by have:=Finset.mem_range.mp ht; omega
  rw [tensor_scale,repeated_component hg htm axis a,← directional_append]
  simpa only [jet,scaledValue,List.length_append,List.length_replicate] using
    factorial_transport w.length t mu q (directional (List.replicate t axis++w) f a)

abbrev Index (d k : ℕ) := Σr : Fin (k+1), Fin r.val → Fin d
abbrev size (d k : ℕ) := Fintype.card (Index d k)

theorem size_formula (d k : ℕ) : size d k=∑r∈Finset.range (k+1),d^r := by
  simp only [size,Index,Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun r:ℕ=>d^r) (k+1)

noncomputable def word {d k : ℕ} (j : Fin (size d k)) : List (Fin d) :=
  List.ofFn ((Fintype.equivFin (Index d k)).symm j).2

theorem word_length {d k : ℕ} (j : Fin (size d k)) : (word j).length≤k := by
  simp only [word,List.length_ofFn]
  exact Nat.le_of_lt_succ ((Fintype.equivFin (Index d k)).symm j).1.isLt

noncomputable def pack {d k : ℕ} (w : List (Fin d)) (hw : w.length≤k) : Fin (size d k) :=
  Fintype.equivFin (Index d k) ⟨⟨w.length,by omega⟩,w.get⟩

theorem word_pack {d k : ℕ} (w : List (Fin d)) (hw : w.length≤k) : word (pack w hw)=w := by
  unfold word pack
  rw [Equiv.symm_apply_apply]
  exact List.ofFn_getElem

noncomputable def extendWord {d k : ℕ} (beta : Fin (size d k)) (axis : Fin d)
    (t : Fin (k-(word beta).length+1)) : Fin (size d k) :=
  pack (List.replicate t.val axis++word beta) (by
    simp only [List.length_append,List.length_replicate]
    have:=word_length beta;have:=t.isLt;omega)

noncomputable def values {d k : ℕ} (mu : ℝ) (f : Space d → ℝ) (a : Space d) : Fin (size d k) → ℝ :=
  fun j=>jet mu f a (word j)

noncomputable def row {d k : ℕ} (axis : Fin d) (q : ℝ) (v : Fin (size d k) → ℝ)
    (beta : Fin (size d k)) : ℝ :=
  ∑t:Fin (k-(word beta).length+1),((t.val+(word beta).length).choose (word beta).length:ℝ)*q^t.val*v (extendWord beta axis t)

noncomputable def matrix {d k : ℕ} (axis : Fin d) (q : ℝ)
    (beta gamma : Fin (size d k)) : ℝ :=
  ∑t:Fin (k-(word beta).length+1),if gamma=extendWord beta axis t then
    ((t.val+(word beta).length).choose (word beta).length:ℝ)*q^t.val else 0

noncomputable def matrixInt {d k : ℕ} (axis : Fin d) (q : ℤ)
    (beta gamma : Fin (size d k)) : ℤ :=
  ∑t:Fin (k-(word beta).length+1),if gamma=extendWord beta axis t then
    ((t.val+(word beta).length).choose (word beta).length:ℤ)*q^t.val else 0

theorem matrix_integral {d k : ℕ} (axis : Fin d) (q : ℤ) (beta gamma : Fin (size d k)) :
    matrix axis (q:ℝ) beta gamma=(matrixInt axis q beta gamma:ℝ) := by
  simp [matrix,matrixInt]

theorem matrix_application {d k : ℕ} (axis : Fin d) (q : ℝ)
    (v : Fin (size d k) → ℝ) (beta : Fin (size d k)) :
    (∑gamma,matrix axis q beta gamma*v gamma)=row axis q v beta := by
  classical
  simp only [matrix,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp [ite_mul]

theorem matrix_compatibility {d k : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f)
    (a : Space d) (axis : Fin d) (mu q : ℝ) (beta : Fin (size d k)) :
    row axis q (values mu f a) beta=
      scaledTaylor mu (word beta).length (k-(word beta).length) (directional (word beta) f) a
        ((mu*q) • basis axis) := by
  have hw:=word_length beta
  have hg : ContDiff ℝ (k-(word beta).length+(word beta).length:ℕ) f := by
    simpa only [Nat.sub_add_cancel hw] using hf
  rw [row_compatibility (word beta) hg]
  simp only [row,values,extendWord,word_pack]
  exact Fin.sum_univ_eq_sum_range (fun t:ℕ=>((t+(word beta).length).choose (word beta).length:ℝ)*q^t*
    jet mu f a (List.replicate t axis++word beta)) (k-(word beta).length+1)

theorem row_sub {d k : ℕ} (axis : Fin d) (q : ℝ) (v u : Fin (size d k) → ℝ)
    (beta : Fin (size d k)) : row axis q (fun j=>v j-u j) beta=row axis q v beta-row axis q u beta := by
  simp only [row,mul_sub,Finset.sum_sub_distrib]

theorem row_bound {d k D : ℕ} (hD : 1≤D) (axis : Fin d) (q C : ℝ)
    (hC : 0≤C) (hq : |q|≤(D:ℝ)) (v : Fin (size d k) → ℝ)
    (hv : ∀j,|v j|≤C) (beta : Fin (size d k)) :
    |row axis q v beta|≤C*MathCan.CommonGateBound.commonBudget k D := by
  have hd : (1:ℝ)≤(D:ℝ) := by exact_mod_cast hD
  have hn:=word_length beta
  have hc : (∑t:Fin (k-(word beta).length+1),(t.val+(word beta).length).choose (word beta).length)=
      (k+1).choose ((word beta).length+1) := by
    rw [Fin.sum_univ_eq_sum_range (fun t:ℕ=>(t+(word beta).length).choose (word beta).length),Nat.sum_range_add_choose]
    congr 1; omega
  have hcr : (∑t:Fin (k-(word beta).length+1),((t.val+(word beta).length).choose (word beta).length:ℝ))=
      ((k+1).choose ((word beta).length+1):ℝ) := by exact_mod_cast hc
  have hp : ∀t:Fin (k-(word beta).length+1),|q^t.val|≤(D:ℝ)^k := by
    intro t
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg q) hq t.val).trans
      (MathCan.CommonGateBound.power_mono_exponent (D:ℝ) hd t.val k (by have:=t.isLt;omega))
  calc
    _ ≤ ∑t:Fin (k-(word beta).length+1),
        |((t.val+(word beta).length).choose (word beta).length:ℝ)*q^t.val*v (extendWord beta axis t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑t:Fin (k-(word beta).length+1),
        ((t.val+(word beta).length).choose (word beta).length:ℝ)*((D:ℝ)^k*C) := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul (hp t) (hv (extendWord beta axis t)) (abs_nonneg _) (by positivity))
        (Nat.cast_nonneg ((t.val+(word beta).length).choose (word beta).length):
          (0:ℝ)≤((t.val+(word beta).length).choose (word beta).length:ℝ))
    _ = ((k+1).choose ((word beta).length+1):ℝ)*((D:ℝ)^k*C) := by rw [← Finset.sum_mul,hcr]
    _ ≤ (2:ℝ)^(k+1)*((D:ℝ)^k*C) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.choose_le_two_pow (k+1) ((word beta).length+1)
    _ = _ := by simp only [MathCan.CommonGateBound.commonBudget,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat];ring

theorem step_norm {d : ℕ} (axis : Fin d) (mu q D : ℝ) (hmu : 0≤mu) (hq : |q|≤D) :
    ‖(mu*q) • basis axis‖≤mu*D := by
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hmu]
  calc
    _ ≤ mu*D*1 := mul_le_mul (mul_le_mul_of_nonneg_left hq hmu) (basis_bound axis)
      (norm_nonneg _) (mul_nonneg hmu ((abs_nonneg q).trans hq))
    _ = _ := by ring

theorem matrix_residual {d k : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f)
    (a : Space d) (axis : Fin d) (mu q D H alpha tau : ℝ)
    (hmu : 0≤mu) (hD : 1≤D) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau)
    (hq : |q|≤D) (scale : mu^((k:ℝ)+alpha)≤2*tau)
    (holder : ∀x y,‖iteratedFDeriv ℝ k f y-iteratedFDeriv ℝ k f x‖≤H*‖y-x‖^alpha)
    (beta : Fin (size d k)) :
    |values mu f (a+(mu*q) • basis axis) beta-row axis q (values mu f a) beta|≤
      (2*H*D^((k:ℝ)+alpha))*tau := by
  have hw:=word_length beta
  have he : directional (word beta) f=component f (word beta).get :=
    funext (directional_component hf (word beta) hw)
  have hb:=MathCan.SharpJet.sharp_jet_transport hf (Nat.sub_add_cancel hw) a ((mu*q) • basis axis)
    (word beta).get mu D H alpha tau hmu hD hH ha htau (step_norm axis mu q D hmu hq) scale
    (fun t _=>holder a _)
  rw [← he,div_le_iff₀ htau] at hb
  rw [matrix_compatibility hf]
  exact hb

theorem value_label {d k : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f)
    (mu : ℝ) (a : Space d) (r : Fin (k+1)) (w : Fin r.val → Fin d) :
    values mu f a (Fintype.equivFin (Index d k) ⟨r,w⟩)=
      mu^r.val/(Nat.factorial r.val:ℝ)*iteratedFDeriv ℝ r.val f a (fun j=>basis (w j)) := by
  unfold values word
  rw [Equiv.symm_apply_apply]
  simp only [jet,scaledValue,List.length_ofFn]
  rw [directional_ofFn hf w (by omega)]

theorem values_bound {d k : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f)
    (mu M : ℝ) (a : Space d) (hmu : 0≤mu) (hmu1 : mu≤1) (hM : 0≤M)
    (bound : ∀r,r≤k → ‖iteratedFDeriv ℝ r f a‖≤M) (j : Fin (size d k)) :
    |values mu f a j|≤M := by
  obtain ⟨i,hi⟩:=(Fintype.equivFin (Index d k)).surjective j
  rw [← hi,value_label hf]
  have hb:=normalized_component_bound a M hM (bound i.1.val (by omega)) i.2
  have hp : mu^i.1.val≤1 := pow_le_one₀ hmu hmu1
  have he : mu^i.1.val/(Nat.factorial i.1.val:ℝ)*iteratedFDeriv ℝ i.1.val f a (fun j=>basis (i.2 j))=
      mu^i.1.val*((Nat.factorial i.1.val:ℝ)⁻¹*iteratedFDeriv ℝ i.1.val f a (fun j=>basis (i.2 j))) := by ring
  rw [he,abs_mul,abs_of_nonneg (pow_nonneg hmu _)]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg hmu _)).trans (mul_le_of_le_one_left hM hp)

noncomputable def evaluate {d k : ℕ} (v : Fin (size d k) → ℝ) (h : Space d) : ℝ :=
  ∑i:Index d k,v (Fintype.equivFin (Index d k) i)*∏j,h (i.2 j)

theorem evaluation_error {d k : ℕ} (v u : Fin (size d k) → ℝ) (h : Space d)
    (epsilon : ℝ) (_he : 0≤epsilon) (hh : ‖h‖≤1) (error : ∀j,|v j-u j|≤epsilon) :
    |evaluate v h-evaluate u h|≤(size d k:ℝ)*epsilon := by
  classical
  unfold evaluate
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑i:Index d k,|(v (Fintype.equivFin _ i)-u (Fintype.equivFin _ i))*∏j,h (i.2 j)| := by
      simpa only [sub_mul] using Finset.abs_sum_le_sum_abs
        (fun i:Index d k=>v (Fintype.equivFin _ i)*(∏j,h (i.2 j))-u (Fintype.equivFin _ i)*(∏j,h (i.2 j))) Finset.univ
    _ ≤ ∑_i:Index d k,epsilon := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,Finset.abs_prod]
      have hcoord : ∀j:Fin d,|h j|≤1 := by
        intro j
        exact (show |h j|≤‖h‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm h j).trans hh
      have hm : (∏j,|h (i.2 j)|)≤1 := Finset.prod_le_one (fun j _=>abs_nonneg _) (fun j _=>hcoord _)
      apply (mul_le_mul_of_nonneg_left hm (abs_nonneg _)).trans
      simpa using error (Fintype.equivFin _ i)
    _ = _ := by simp [size]

theorem evaluation_values {d k : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f)
    (mu : ℝ) (hmu : 0<mu) (a h : Space d) :
    evaluate (k:=k) (values (k:=k) mu f a) (mu⁻¹ • h)=tensorPolynomial f k a h := by
  classical
  unfold evaluate
  rw [Fintype.sum_sigma]
  unfold tensorPolynomial
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  rw [tensor_expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [value_label hf]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hc : mu^r.val*(mu⁻¹)^r.val=1 := by rw [← mul_pow,mul_inv_cancel₀ hmu.ne',one_pow]
  rw [show mu^r.val/(Nat.factorial r.val:ℝ)*iteratedFDeriv ℝ r.val f a (fun j=>basis (w j))*
      ((mu⁻¹)^r.val*∏j,h (w j))=
      (mu^r.val*(mu⁻¹)^r.val)*((Nat.factorial r.val:ℝ)⁻¹*(∏j,h (w j))*
        iteratedFDeriv ℝ r.val f a (fun j=>basis (w j))) by ring,hc]
  ring

end MathCan.WordTransport

namespace MathCan.WordCapture
open MathCan.WordTransport
open MathCan.MultivariateTaylor (Space basis tensorPolynomial)
open MathCan.JetSynthesis MathCan.FrameSynthesis MathCan.TaylorTransport
open MathCan.SpatialClipped MathCan.DecodedJetCapture MathCan.TaylorFrame
open MathCan.HammingSelector MathCan.SentinelDecoder MathCan.CommonGateBound
open MathCan.SpatialScalar MathCan.SpatialNormalized MathCan.SpatialRouting
set_option autoImplicit false

abbrev Motion (d D : ℕ) := Fin d × Bool × Fin (D+1)
abbrev tagCount (d D : ℕ) := Fintype.card (Motion d D)
abbrev Tag (d D : ℕ) := Fin (tagCount d D)

theorem finite_parameters (d k D : ℕ) (B : ℝ) :
    ∃N p a:ℕ,B+commonBudget (R:=ℝ) k D/2+1/2≤(N:ℝ) ∧ tagCount d D<2^p ∧ 2*N<2^a :=
  MathCan.MultivariateCapture.finite_frame_parameters (B+commonBudget k D/2) (tagCount d D)
noncomputable def motion {d D : ℕ} (tag : Tag d D) : Motion d D :=
  (Fintype.equivFin (Motion d D)).symm tag
noncomputable def axis {d D : ℕ} (tag : Tag d D) : Fin d := (motion tag).1
noncomputable def amount {d D : ℕ} (tag : Tag d D) : ℝ :=
  signedStep (motion tag).2.1 (motion tag).2.2.val
noncomputable def predict {d k D : ℕ} (tag : Tag d D) (v : Fin (WordTransport.size d k) → ℝ) : Fin (WordTransport.size d k) → ℝ :=
  row (axis tag) (amount tag) v

theorem amount_bound {d D : ℕ} (tag : Tag d D) : |amount tag|≤(D:ℝ) := by
  exact abs_le.mpr (signed_step_bound _ _ D (by have:=(motion tag).2.2.isLt;omega))

theorem predict_bound {d k D : ℕ} (hD : 1≤D) (C : ℝ) (hC : 0≤C) (tag : Tag d D)
    (v : Fin (WordTransport.size d k) → ℝ) (hv : ∀j,|v j|≤C) (beta : Fin (WordTransport.size d k)) :
    |predict tag v beta|≤C*commonBudget k D := row_bound hD _ _ C hC (amount_bound tag) v hv beta

noncomputable def quantize {d k D : ℕ} (C tau : ℝ) (tag : Tag d D)
    (target v : Fin (WordTransport.size d k) → ℝ) : Fin (WordTransport.size d k) → ℝ :=
  fun beta=>symmetricClip C (rounded tau (target beta) (predict tag v beta))

noncomputable def packet {d k D : ℕ} (p a N : ℕ) (tau : ℝ) (tag : Tag d D)
    (target v : Fin (WordTransport.size d k) → ℝ) : List Bool :=
  framePayload p a tag.val (fun beta=>code N (correction tau (target beta) (predict tag v beta)))

noncomputable def reader {d k D : ℕ} (p a : ℕ) (C centre tau : ℝ)
    (v : Fin (WordTransport.size d k) → ℝ) (bits : List ℝ) : Fin (WordTransport.size d k) → ℝ := fun beta=>
  chooseScalar (tagCount d D) p (C*commonBudget k D) (bits.take p)
    (fun q=>if h:q<tagCount d D then predict ⟨q,h⟩ v beta else 0)+
      tau*(unsignedLE (blockAt a (bits.drop p) beta.val)-centre)

theorem innovation {d k D : ℕ} (hD : 1≤D) (tau B : ℝ) (htau : 0<tau)
    (tag : Tag d D) (target u v : Fin (WordTransport.size d k) → ℝ)
    (residual : ∀j,|target j-predict tag u j|≤B*tau) (accurate : ∀j,|v j-u j|≤tau/2)
    (beta : Fin (WordTransport.size d k)) : |(target beta-predict tag v beta)/tau|≤B+commonBudget k D/2 := by
  have hp:=predict_bound hD (tau/2) (by positivity) tag (fun j=>v j-u j) accurate beta
  simp only [predict,row_sub] at hp
  have ht:=abs_sub_le (target beta) (predict tag u beta) (predict tag v beta)
  rw [abs_sub_comm (predict tag u beta)] at ht
  rw [abs_div,abs_of_pos htau,div_le_iff₀ htau]
  have hr:=residual beta
  simp only [predict] at ht hr ⊢
  nlinarith

theorem packet_update {d k D : ℕ} (hD : 1≤D) (p a N : ℕ)
    (hTags : tagCount d D<2^p) (hwidth : 2*N<2^a) (C tau B : ℝ) (hC : 0≤C) (htau : 0<tau)
    (hN : B+commonBudget k D/2+1/2≤(N:ℝ)) (tag : Tag d D) (target u v : Fin (WordTransport.size d k) → ℝ)
    (hv : ∀j,-C≤v j ∧ v j≤C)
    (residual : ∀j,|target j-predict tag u j|≤B*tau) (accurate : ∀j,|v j-u j|≤tau/2) :
    boundedUpdate C (reader (D:=D) p a C (N:ℝ) tau) v ((packet p a N tau tag target v).map bit)=
      quantize C tau tag target v := by
  have hc:∀beta,-(N:ℤ)≤correction tau (target beta) (predict tag v beta) ∧
      correction tau (target beta) (predict tag v beta)≤(N:ℤ) := by
    intro beta
    exact correction_bound tau _ _ _ N (innovation hD tau B htau tag target u v residual accurate beta) hN
  have hcor:∀beta,code N (correction tau (target beta) (predict tag v beta))<2^a :=
    fun beta=>code_bound N a _ (hc beta) hwidth
  funext beta
  simp only [boundedUpdate,reader,packet]
  rw [frame_amplitude_prefix,frame_correction_value p a tag.val _ hcor beta]
  rw [choose_scalar_exact (tagCount d D) p tag.val hTags (by omega) _ _ (by
    intro q hq
    by_cases h:q<tagCount d D
    · simp only [dif_pos h]
      exact abs_le.mp (predict_bound hD C hC ⟨q,h⟩ v (fun j=>abs_le.mpr (hv j)) beta)
    · simp only [dif_neg h]
      have hb:=mul_nonneg hC (common_budget_nonnegative (R:=ℝ) k D)
      exact ⟨by linarith,by linarith⟩)]
  simp only [dif_pos tag.isLt]
  rw [code_decode N _ (hc beta).1]
  rfl

def Residuals {d k D : ℕ} (tau B : ℝ) : List (Tag d D) → (ℕ → Fin (WordTransport.size d k) → ℝ) → Prop
  | [],_ => True
  | tag::tail,u => (∀beta,|u 1 beta-predict tag (u 0) beta|≤B*tau) ∧
      Residuals tau B tail (fun i=>u (i+1))

noncomputable def frames {d k D : ℕ} (p a N : ℕ) (C tau : ℝ) :
    List (Tag d D) → (ℕ → Fin (WordTransport.size d k) → ℝ) → (Fin (WordTransport.size d k) → ℝ) → List (List Bool)
  | [],_,_ => []
  | tag::tail,u,v => packet p a N tau tag (u 1) v ::
      frames p a N C tau tail (fun i=>u (i+1)) (quantize C tau tag (u 1) v)

theorem frames_length {d k D : ℕ} (p a N : ℕ) (C tau : ℝ) (tags : List (Tag d D))
    (u : ℕ → Fin (WordTransport.size d k) → ℝ) (v : Fin (WordTransport.size d k) → ℝ) :
    (frames p a N C tau tags u v).length=tags.length := by
  induction tags generalizing u v with
  | nil => rfl
  | cons tag tail ih => simp only [frames,List.length_cons];rw [ih]

theorem reference_accuracy {d k D : ℕ} (hD : 1≤D) (p a N : ℕ)
    (hTags : tagCount d D<2^p) (hwidth : 2*N<2^a) (C tau B : ℝ) (hC : 0≤C) (htau : 0<tau)
    (hN : B+commonBudget k D/2+1/2≤(N:ℝ)) (tags : List (Tag d D))
    (u : ℕ → Fin (WordTransport.size d k) → ℝ) (hr : Residuals tau B tags u)
    (bounded : ∀i,i≤tags.length → ∀j,-C≤u i j ∧ u i j≤C)
    (v : Fin (WordTransport.size d k) → ℝ) (hv : ∀j,-C≤v j ∧ v j≤C) (accurate : ∀j,|v j-u 0 j|≤tau/2) :
    ∀i,i≤tags.length → ∀beta,
      |referenceJetAt C (reader (D:=D) p a C (N:ℝ) tau) (frames p a N C tau tags u v) v i beta-u i beta|≤tau/2 := by
  induction tags generalizing u v with
  | nil =>
    intro i hi
    have he:i=0:=by simpa using hi
    subst i
    exact accurate
  | cons tag tail ih =>
    intro i hi
    cases i with
    | zero => exact accurate
    | succ i =>
      simp only [frames,referenceJetAt]
      rw [packet_update hD p a N hTags hwidth C tau B hC htau hN tag (u 1) (u 0) v hv hr.1 accurate]
      apply ih (fun j=>u (j+1)) hr.2 (fun j hj=>bounded (j+1) (by simp only [List.length_cons];omega))
        (quantize C tau tag (u 1) v) (fun j=>symmetric_clip_range C _ hC)
        (fun j=>clipped_round_error C tau _ _ hC htau (bounded 1 (by simp) j))
        i (by simp only [List.length_cons] at hi;omega)

noncomputable def captured {d k D : ℕ} (spatialN K p a N : ℕ) (delta C tau : ℝ)
    (sites : List (Site ℝ)) (tags : List (Tag d D)) (u : ℕ → Fin (WordTransport.size d k) → ℝ) : Fin (WordTransport.size d k) → ℝ :=
  let v:=initial C tau (u 0)
  let fs:=frames p a N C tau tags u v
  fun beta=>captureStream C (((K^sites.length:ℕ):ℝ)*clippedCircuit K (decodedDigits spatialN K delta sites))
    (fun i=>decodedJetAt C (reader (D:=D) p a C (N:ℝ) tau) (fs.map List.length) (MathCan.SentinelDecoder.word fs.flatten) v i beta)
    (K^sites.length)

theorem captured_accuracy {d k D : ℕ} (hD : 1≤D) (spatialN K p a N : ℕ)
    (hK : 0<K) (hTags : tagCount d D<2^p) (hwidth : 2*N<2^a)
    (delta C tau B : ℝ) (hdelta : 0<delta) (hC : 0≤C) (htau : 0<tau)
    (hN : B+commonBudget k D/2+1/2≤(N:ℝ)) (sites : List (Site ℝ))
    (safe : validSites spatialN K delta sites) (tags : List (Tag d D))
    (alignment : tags.length+1=K^sites.length) (u : ℕ → Fin (WordTransport.size d k) → ℝ)
    (hr : Residuals tau B tags u) (bounded : ∀i,i≤tags.length → ∀j,-C≤u i j ∧ u i j≤C) :
    ∀beta,|captured spatialN K p a N delta C tau sites tags u beta-
      u (snakeRank K (sites.map Site.fine)) beta|≤tau/2 := by
  let v:=initial C tau (u 0)
  let fs:=frames p a N C tau tags u v
  have hc:=decoded_spatial_capture spatialN K (WordTransport.size d k) hK delta hdelta sites safe C hC
    (reader (D:=D) p a C (N:ℝ) tau) fs (by rw [frames_length];exact alignment) v (initial_range C tau hC _)
  have he : captured spatialN K p a N delta C tau sites tags u=
      referenceJetAt C (reader (D:=D) p a C (N:ℝ) tau) fs v (snakeRank K (sites.map Site.fine)) := hc.2
  rw [he]
  exact reference_accuracy hD p a N hTags hwidth C tau B hC htau hN tags u hr bounded v
    (initial_range C tau hC _) (initial_accuracy C tau hC htau _ (bounded 0 (by omega))) _
    (by simpa only [fs,frames_length] using hc.1)

noncomputable def anchors {d D : ℕ} (mu : ℝ) : List (Tag d D) → Space d → ℕ → Space d
  | _,a,0 => a
  | [],_,_+1 => 0
  | tag::tail,a,i+1 => anchors mu tail (a+(mu*amount tag) • basis (axis tag)) i

noncomputable def targets {d k D : ℕ} (mu : ℝ) (f : Space d → ℝ)
    (tags : List (Tag d D)) (a : Space d) : ℕ → Fin (WordTransport.size d k) → ℝ :=
  fun i=>values mu f (anchors mu tags a i)

theorem targets_residuals {d k D : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ k f)
    (hD : 1≤D) (mu H alpha tau : ℝ) (hmu : 0≤mu) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau)
    (scale : mu^((k:ℝ)+alpha)≤2*tau)
    (holder : ∀x y,‖iteratedFDeriv ℝ k f y-iteratedFDeriv ℝ k f x‖≤H*‖y-x‖^alpha)
    (tags : List (Tag d D)) (a : Space d) :
    Residuals tau (2*H*(D:ℝ)^((k:ℝ)+alpha)) tags (targets (k:=k) mu f tags a) := by
  induction tags generalizing a with
  | nil => trivial
  | cons tag tail ih =>
    constructor
    · intro beta
      simpa only [targets,anchors,predict] using matrix_residual hf a (axis tag) mu (amount tag) (D:ℝ)
        H alpha tau hmu (by exact_mod_cast hD) hH ha htau (amount_bound tag) scale holder beta
    · exact ih (a+(mu*amount tag) • basis (axis tag))

theorem normalized_approximation {d n : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ (n+1) f)
    (mu H alpha tau rho : ℝ) (hmu : 0<mu) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau)
    (a x : Space d) (hdist : ‖x-a‖≤rho) (hrho : rho≤mu)
    (holder : ∀y z,‖iteratedFDeriv ℝ (n+1) f z-iteratedFDeriv ℝ (n+1) f y‖≤H*‖z-y‖^alpha)
    (v : Fin (WordTransport.size d (n+1)) → ℝ)
    (accurate : ∀j,|v j-values mu f a j|≤tau/2) :
    |f x-WordTransport.evaluate v (mu⁻¹ • (x-a))|≤
      H*rho^(((n+1:ℕ):ℝ)+alpha)/(Nat.factorial (n+1):ℝ)+(WordTransport.size d (n+1):ℝ)*(tau/2) := by
  have hh : ‖mu⁻¹ • (x-a)‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hmu)]
    calc
      _ ≤ mu⁻¹*mu := mul_le_mul_of_nonneg_left (hdist.trans hrho) (inv_nonneg.mpr hmu.le)
      _ = 1 := inv_mul_cancel₀ hmu.ne'
  have he:=evaluation_error v (values mu f a) (mu⁻¹ • (x-a)) (tau/2) (by positivity) hh accurate
  rw [evaluation_values hf mu hmu,abs_sub_comm] at he
  have ht:=MathCan.MultivariateHolder.holder_tensor_remainder hf a (x-a) H alpha hH ha (fun t _=>holder a _)
  simp only [add_sub_cancel] at ht
  have hp:=Real.rpow_le_rpow (norm_nonneg (x-a)) hdist (show 0≤((n+1:ℕ):ℝ)+alpha by positivity)
  have hb:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hH) (Nat.cast_nonneg (Nat.factorial (n+1)))
  exact (abs_sub_le (f x) (tensorPolynomial f (n+1) a (x-a)) (WordTransport.evaluate v (mu⁻¹ • (x-a)))).trans
    (add_le_add (ht.trans hb) he)

/-- General higher-order decoded approximation. The normalized matrix and its
analytic residual are proved above; neither is an assumption of this theorem. -/
theorem decoded_approximation {d n D : ℕ} {f : Space d → ℝ} (hf : ContDiff ℝ (n+1) f)
    (hD : 1≤D) (spatialN K p a N : ℕ) (hK : 0<K) (hTags : tagCount d D<2^p)
    (hwidth : 2*N<2^a) (delta mu M H alpha tau rho : ℝ)
    (hdelta : 0<delta) (hmu : 0<mu) (hmu1 : mu≤1) (hM : 0≤M) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau)
    (scale : mu^(((n+1:ℕ):ℝ)+alpha)≤2*tau)
    (hN : 2*H*(D:ℝ)^(((n+1:ℕ):ℝ)+alpha)+commonBudget (n+1) D/2+1/2≤(N:ℝ))
    (holder : ∀y z,‖iteratedFDeriv ℝ (n+1) f z-iteratedFDeriv ℝ (n+1) f y‖≤H*‖z-y‖^alpha)
    (sites : List (Site ℝ)) (safe : validSites spatialN K delta sites)
    (tags : List (Tag d D)) (alignment : tags.length+1=K^sites.length) (a0 x : Space d)
    (bound : ∀i,i≤tags.length → ∀r,r≤n+1 → ‖iteratedFDeriv ℝ r f (anchors mu tags a0 i)‖≤M)
    (hdist : ‖x-anchors mu tags a0 (snakeRank K (sites.map Site.fine))‖≤rho) (hrho : rho≤mu) :
    |f x-WordTransport.evaluate
      (captured spatialN K p a N delta M tau sites tags (targets (k:=n+1) mu f tags a0))
      (mu⁻¹ • (x-anchors mu tags a0 (snakeRank K (sites.map Site.fine))))|≤
      H*rho^(((n+1:ℕ):ℝ)+alpha)/(Nat.factorial (n+1):ℝ)+(WordTransport.size d (n+1):ℝ)*(tau/2) := by
  have hb : ∀i,i≤tags.length → ∀j,-M≤targets (k:=n+1) mu f tags a0 i j ∧
      targets (k:=n+1) mu f tags a0 i j≤M := by
    intro i hi j
    exact abs_le.mp (values_bound hf mu M _ hmu.le hmu1 hM (bound i hi) j)
  have hr:=targets_residuals hf hD mu H alpha tau hmu.le hH ha htau scale holder tags a0
  have hc:=captured_accuracy hD spatialN K p a N hK hTags hwidth delta M tau
    (2*H*(D:ℝ)^(((n+1:ℕ):ℝ)+alpha)) hdelta hM htau hN sites safe tags alignment
    (targets (k:=n+1) mu f tags a0) hr hb
  exact normalized_approximation hf mu H alpha tau rho hmu hH ha htau _ x hdist hrho holder _ hc

end MathCan.WordCapture
