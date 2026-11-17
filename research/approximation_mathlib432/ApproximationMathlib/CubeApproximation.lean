import ApproximationMathlib.WordTransport
import MathCan.SpatialInterface

/-! Intrinsic derivatives on the closed cube and spatially covered Taylor jets.
All differentiation at faces is within the cube. -/
namespace MathCan.CubeTaylor
open Set MathCan.MultivariateTaylor MathCan.MultivariateBounds MathCan.TaylorFoundation
set_option autoImplicit false

def cube (d : ℕ) : Set (Space d) := {x | ∀j : Fin d, (0:ℝ)≤x j ∧ x j≤(1:ℝ)}

theorem cube_convex (d : ℕ) : Convex ℝ (cube d) := by
  intro x hx y hy a b ha hb hab j
  change 0≤a*x j+b*y j ∧ a*x j+b*y j≤1
  constructor
  · exact add_nonneg (mul_nonneg ha (hx j).1) (mul_nonneg hb (hy j).1)
  · calc
      _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left (hx j).2 ha)
        (mul_le_mul_of_nonneg_left (hy j).2 hb)
      _ = 1 := by linarith

theorem cube_uniqueDiff (d : ℕ) : UniqueDiffOn ℝ (cube d) := by
  apply uniqueDiffOn_convex (cube_convex d)
  refine ⟨fun _=>1/2, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (fun _:Fin d=>(1/2:ℝ)) (by norm_num : (0:ℝ)<1/2))
  intro x hx j
  have h := (norm_le_pi_norm (x-(fun _:Fin d=>(1/2:ℝ))) j).trans_lt hx
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h
  exact ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩

theorem cube_segment {d : ℕ} {a x : Space d} (ha : a∈cube d) (hx : x∈cube d)
    {t : ℝ} (ht : t∈uIcc (0:ℝ) 1) : a+t • (x-a)∈cube d := by
  rw [uIcc_of_le (by norm_num)] at ht
  have h := cube_convex d ha hx (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
  convert h using 1 <;> ext j <;> simp <;> ring

noncomputable def dir {d : ℕ} (s : Set (Space d)) : List (Space d) → (Space d→ℝ) → Space d→ℝ
  | [], f => f
  | v::w, f => fun x=>fderivWithin ℝ (dir s w f) s x v

theorem dir_smooth {d m : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    (w : List (Space d)) {f : Space d→ℝ} (hf : ContDiffOn ℝ (m+w.length:ℕ) f s) :
    ContDiffOn ℝ m (dir s w f) s := by
  induction w generalizing m with
  | nil => simpa [dir] using hf
  | cons v w ih =>
    have hh : ContDiffOn ℝ (m+1:ℕ) (dir s w f) s :=
      ih (m:=m+1) (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf)
    exact (hh.fderivWithin hs (by norm_cast)).clm_apply contDiffOn_const

theorem dir_tensor {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (w : List (Space d)) (hw : w.length≤k)
    {x : Space d} (hx : x∈s) :
    dir s w f x=iteratedFDerivWithin ℝ w.length f s x w.get := by
  induction w generalizing x with
  | nil => simp [dir]
  | cons v w ih =>
    have he : ∀y∈s, dir s w f y=iteratedFDerivWithin ℝ w.length f s y w.get :=
      fun y hy=>ih (by simp only [List.length_cons] at hw; omega) hy
    have hd : DifferentiableOn ℝ (iteratedFDerivWithin ℝ w.length f s) s :=
      hf.differentiableOn_iteratedFDerivWithin (by exact_mod_cast (show w.length<k by simp only [List.length_cons] at hw; omega)) hs
    simp only [dir,List.length_cons]
    rw [fderivWithin_congr' he hx,
      fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (hd x hx)]
    rfl

theorem line_smooth {d k : ℕ} {s : Set (Space d)} {f : Space d→ℝ}
    (hf : ContDiffOn ℝ k f s) (a h : Space d) (b : ℝ)
    (inside : ∀t∈uIcc (0:ℝ) b, a+t • h∈s) :
    ContDiffOn ℝ k (along f a h) (uIcc (0:ℝ) b) :=
  hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn inside

theorem line_derivatives {d k r : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (w : List (Space d))
    (hr : r+w.length≤k) (a h : Space d) (b : ℝ) (hb : b≠0)
    (inside : ∀t∈uIcc (0:ℝ) b, a+t • h∈s) {t : ℝ} (ht : t∈uIcc (0:ℝ) b) :
    iteratedDerivWithin r (along (dir s w f) a h) (uIcc (0:ℝ) b) t=
      dir s (List.replicate r h++w) f (a+t • h) := by
  have hu : UniqueDiffOn ℝ (uIcc (0:ℝ) b) := uniqueDiffOn_Icc (by grind)
  induction r generalizing t with
  | zero => simp [dir,along]
  | succ r ih =>
    rw [iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun y hy=>ih (by omega) hy) (ih (by omega) ht)]
    have hg : ContDiffOn ℝ 1 (dir s (List.replicate r h++w) f) s :=
      dir_smooth hs _ (hf.of_le (by simp only [List.length_append,List.length_replicate]; exact_mod_cast (show 1+(r+w.length)≤k by omega)))
    have hd := (hg.differentiableOn (by norm_num) _ (inside t ht)).hasFDerivWithinAt
    have hl : HasDerivAt (fun t:ℝ=>a+t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add a
    have hc := hd.comp_hasDerivWithinAt t hl.hasDerivWithinAt inside
    simpa [List.replicate_succ,dir,Function.comp_def] using hc.derivWithin (hu t ht)

theorem dir_ofFn {d k r : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (w : Fin r→Space d) (hr : r≤k)
    {x : Space d} (hx : x∈s) :
    dir s (List.ofFn w) f x=iteratedFDerivWithin ℝ r f s x w := by
  induction r generalizing x with
  | zero => simp [dir]
  | succ r ih =>
    have he : ∀y∈s, dir s (List.ofFn (fun i:Fin r=>w i.succ)) f y=
        iteratedFDerivWithin ℝ r f s y (fun i=>w i.succ) := fun y hy=>ih _ (by omega) hy
    have hd := hf.differentiableOn_iteratedFDerivWithin
      (m:=r) (by exact_mod_cast (show r<k by omega)) hs
    rw [List.ofFn_succ]
    simp only [dir]
    rw [fderivWithin_congr' he hx,
      fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (hd x hx)]
    rfl

noncomputable def polynomial {d : ℕ} (s : Set (Space d)) (f : Space d→ℝ)
    (k : ℕ) (a h : Space d) : ℝ :=
  ∑r∈Finset.range (k+1),(Nat.factorial r:ℝ)⁻¹*iteratedFDerivWithin ℝ r f s a (fun _=>h)

theorem line_polynomial {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (a h : Space d)
    (inside : ∀t∈uIcc (0:ℝ) 1, a+t • h∈s) :
    taylorWithinEval (along f a h) k (uIcc (0:ℝ) 1) 0 1=polynomial s f k a h := by
  rw [MathCan.TaylorFoundation.taylor_within_apply]
  unfold polynomial
  apply Finset.sum_congr rfl
  intro r hr
  have hrk : r≤k := by have:=Finset.mem_range.mp hr; omega
  have he := line_derivatives hs hf [] (by simpa using hrk) a h 1 (by norm_num) inside left_mem_uIcc
  have hd := dir_ofFn hs hf (fun _:Fin r=>h) hrk (by simpa using inside 0 left_mem_uIcc)
  simp only [List.ofFn_const] at hd
  simp only [dir,List.append_nil,zero_smul,add_zero] at he
  rw [he,hd]
  simp

theorem line_tensor {d k r : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (hr : r≤k) (a h : Space d)
    (inside : ∀t∈uIcc (0:ℝ) 1, a+t • h∈s) {t : ℝ} (ht : t∈uIcc (0:ℝ) 1) :
    iteratedDerivWithin r (along f a h) (uIcc (0:ℝ) 1) t=
      iteratedFDerivWithin ℝ r f s (a+t • h) (fun _=>h) := by
  have he := line_derivatives hs hf [] (by simpa using hr) a h 1 (by norm_num) inside ht
  have hd := dir_ofFn hs hf (fun _:Fin r=>h) hr (inside t ht)
  simp only [List.ofFn_const] at hd
  simp only [dir,List.append_nil] at he
  exact he.trans hd

theorem holder_remainder {d n : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ (n+1) f s) (a h : Space d)
    (H alpha : ℝ) (hH : 0≤H) (ha : 0≤alpha)
    (inside : ∀t∈uIcc (0:ℝ) 1, a+t • h∈s)
    (holder : ∀t∈uIcc (0:ℝ) 1,
      ‖iteratedFDerivWithin ℝ (n+1) f s (a+t • h)-iteratedFDerivWithin ℝ (n+1) f s a‖≤
        H*‖a+t • h-a‖^alpha) :
    |f (a+h)-polynomial s f (n+1) a h|≤
      H*‖h‖^(((n+1:ℕ):ℝ)+alpha)/(Nat.factorial (n+1):ℝ) := by
  have hg := line_smooth hf a h 1 inside
  have hd : ∀t∈uIcc (0:ℝ) 1,
      |iteratedDerivWithin (n+1) (along f a h) (uIcc (0:ℝ) 1) t-
        iteratedDerivWithin (n+1) (along f a h) (uIcc (0:ℝ) 1) 0|≤
        (H*‖h‖^(((n+1:ℕ):ℝ)+alpha))*|t-0|^alpha := by
    intro t ht
    rw [line_tensor hs hf (by rfl) a h inside ht,
      line_tensor hs hf (by rfl) a h inside left_mem_uIcc]
    simp only [zero_smul,add_zero,sub_zero]
    have hb := diagonal_bound
      (iteratedFDerivWithin ℝ (n+1) f s (a+t • h)-iteratedFDerivWithin ℝ (n+1) f s a) h
    simp only [ContinuousMultilinearMap.sub_apply] at hb
    calc
      _ ≤ ‖iteratedFDerivWithin ℝ (n+1) f s (a+t • h)-iteratedFDerivWithin ℝ (n+1) f s a‖*‖h‖^(n+1) := hb
      _ ≤ (H*‖a+t • h-a‖^alpha)*‖h‖^(n+1) :=
        mul_le_mul_of_nonneg_right (holder t ht) (pow_nonneg (norm_nonneg h) _)
      _ = _ := by
        simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
        rw [Real.mul_rpow (abs_nonneg t) (norm_nonneg h),
          Real.rpow_add_of_nonneg (norm_nonneg h) (Nat.cast_nonneg _) ha,Real.rpow_natCast]
        ring
  have hr := MathCan.SmoothTaylor.holder_remainder_bound
    (mul_nonneg hH (Real.rpow_nonneg (norm_nonneg h) _)) ha hg hd
  rw [line_polynomial hs hf a h inside] at hr
  simpa [along] using hr

noncomputable def values {d k : ℕ} (s : Set (Space d)) (mu : ℝ) (f : Space d→ℝ)
    (a : Space d) (j : Fin (MathCan.WordTransport.size d k)) : ℝ :=
  let i := (Fintype.equivFin (MathCan.WordTransport.Index d k)).symm j
  mu^i.1.val/(Nat.factorial i.1.val:ℝ)*iteratedFDerivWithin ℝ i.1.val f s a (fun r=>basis (i.2 r))

theorem value_label {d k : ℕ} (s : Set (Space d)) (mu : ℝ) (f : Space d→ℝ)
    (a : Space d) (r : Fin (k+1)) (w : Fin r.val→Fin d) :
    values s mu f a (Fintype.equivFin (MathCan.WordTransport.Index d k) ⟨r,w⟩)=
      mu^r.val/(Nat.factorial r.val:ℝ)*iteratedFDerivWithin ℝ r.val f s a (fun j=>basis (w j)) := by
  unfold values
  rw [Equiv.symm_apply_apply]

theorem evaluation_values {d k : ℕ} (s : Set (Space d)) (f : Space d→ℝ)
    (mu : ℝ) (hmu : 0<mu) (a h : Space d) :
    MathCan.WordTransport.evaluate (k:=k) (values s mu f a) (mu⁻¹ • h)=polynomial s f k a h := by
  classical
  unfold MathCan.WordTransport.evaluate
  rw [Fintype.sum_sigma]
  unfold polynomial
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  rw [tensor_expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [value_label]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hc : mu^r.val*(mu⁻¹)^r.val=1 := by rw [← mul_pow,mul_inv_cancel₀ hmu.ne',one_pow]
  rw [show mu^r.val/(Nat.factorial r.val:ℝ)*iteratedFDerivWithin ℝ r.val f s a (fun j=>basis (w j))*
      ((mu⁻¹)^r.val*∏j,h (w j))=
      (mu^r.val*(mu⁻¹)^r.val)*((Nat.factorial r.val:ℝ)⁻¹*(∏j,h (w j))*
        iteratedFDerivWithin ℝ r.val f s a (fun j=>basis (w j))) by ring,hc]
  ring

noncomputable def axes {d : ℕ} (s : Set (Space d)) (w : List (Fin d))
    (f : Space d→ℝ) : Space d→ℝ := dir s (w.map basis) f

theorem axes_tensor {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (w : List (Fin d)) (hw : w.length≤k)
    {x : Space d} (hx : x∈s) :
    axes s w f x=iteratedFDerivWithin ℝ w.length f s x (fun i=>basis (w.get i)) := by
  have he : w.map basis=List.ofFn (fun i:Fin w.length=>basis (w.get i)) := by
    change w.map basis=List.ofFn (basis ∘ w.get)
    rw [← List.map_ofFn]
    congr 1
    exact List.ofFn_getElem.symm
  rw [axes,he]
  exact dir_ofFn hs hf _ hw hx

theorem axes_difference {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (w : List (Fin d)) (hw : w.length≤k)
    {x y : Space d} (hx : x∈s) (hy : y∈s) :
    |axes s w f y-axes s w f x|≤
      ‖iteratedFDerivWithin ℝ w.length f s y-iteratedFDerivWithin ℝ w.length f s x‖ := by
  rw [axes_tensor hs hf w hw hy,axes_tensor hs hf w hw hx]
  simpa only [ContinuousMultilinearMap.sub_apply] using component_bound
    (iteratedFDerivWithin ℝ w.length f s y-iteratedFDerivWithin ℝ w.length f s x) w.get

theorem values_axes {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (mu : ℝ) {a : Space d} (ha : a∈s)
    (j : Fin (MathCan.WordTransport.size d k)) :
    values s mu f a j=mu^(MathCan.WordTransport.word j).length/
      (Nat.factorial (MathCan.WordTransport.word j).length:ℝ)*axes s (MathCan.WordTransport.word j) f a := by
  unfold values MathCan.WordTransport.word
  generalize (Fintype.equivFin (MathCan.WordTransport.Index d k)).symm j=i
  rcases i with ⟨r,w⟩
  simp only [List.length_ofFn,axes,List.map_ofFn]
  rw [dir_ofFn hs hf _ (by have:=r.isLt; omega) ha]
  rfl

noncomputable def axisPolynomial {d k : ℕ} (s : Set (Space d)) (mu : ℝ)
    (f : Space d→ℝ) (a : Space d) (axis : Fin d) (q : ℝ)
    (beta : Fin (MathCan.WordTransport.size d k)) : ℝ :=
  let w := MathCan.WordTransport.word beta
  mu^w.length/(Nat.factorial w.length:ℝ)*
    ∑t∈Finset.range (k-w.length+1),(Nat.factorial t:ℝ)⁻¹*(mu*q)^t*
      axes s (List.replicate t axis++w) f a

theorem row_compatibility {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (mu : ℝ) {a : Space d} (ha : a∈s)
    (axis : Fin d) (q : ℝ) (beta : Fin (MathCan.WordTransport.size d k)) :
    MathCan.WordTransport.row axis q (values s mu f a) beta=axisPolynomial s mu f a axis q beta := by
  unfold MathCan.WordTransport.row axisPolynomial
  rw [Finset.mul_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  rw [values_axes hs hf mu ha]
  simp only [MathCan.WordTransport.extendWord,MathCan.WordTransport.word_pack,
    List.length_append,List.length_replicate]
  simpa only [mul_assoc] using (MathCan.WordTransport.factorial_transport
    (MathCan.WordTransport.word beta).length t.val mu q
      (axes s (List.replicate t.val axis++MathCan.WordTransport.word beta) f a)).symm

theorem row_zero {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (mu : ℝ) {a : Space d} (ha : a∈s)
    (axis : Fin d) (beta : Fin (MathCan.WordTransport.size d k)) :
    MathCan.WordTransport.row axis 0 (values s mu f a) beta=values s mu f a beta := by
  rw [row_compatibility hs hf mu ha,values_axes hs hf mu ha]
  dsimp only [axisPolynomial]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro t _ ht; simp [ht]
  · simp

theorem axis_line_polynomial {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (mu : ℝ) (a : Space d)
    (axis : Fin d) (q : ℝ) (hb : mu*q≠0)
    (inside : ∀t∈uIcc (0:ℝ) (mu*q),a+t • basis axis∈s)
    (beta : Fin (MathCan.WordTransport.size d k)) :
    axisPolynomial s mu f a axis q beta=
      mu^(MathCan.WordTransport.word beta).length/(Nat.factorial (MathCan.WordTransport.word beta).length:ℝ)*
      taylorWithinEval (along (axes s (MathCan.WordTransport.word beta) f) a (basis axis))
        (k-(MathCan.WordTransport.word beta).length) (uIcc (0:ℝ) (mu*q)) 0 (mu*q) := by
  dsimp only [axisPolynomial]
  congr 1
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro t ht
  have hr : t+(MathCan.WordTransport.word beta).length≤k := by
    have:=MathCan.WordTransport.word_length beta
    have:=Finset.mem_range.mp ht
    omega
  have he:=line_derivatives hs hf ((MathCan.WordTransport.word beta).map basis)
    (by simpa using hr) a (basis axis) (mu*q) hb inside left_mem_uIcc
  simp only [axes,List.map_append,List.map_replicate,zero_smul,add_zero] at he ⊢
  rw [he]
  simp
  <;> ring

theorem axis_line_holder {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (w : List (Fin d)) (hw : w.length≤k)
    (a : Space d) (axis : Fin d) (b H alpha : ℝ) (hb : b≠0) (hH : 0≤H) (ha : 0≤alpha)
    (inside : ∀t∈uIcc (0:ℝ) b,a+t • basis axis∈s)
    (holder : ∀x∈s,∀y∈s,
      ‖iteratedFDerivWithin ℝ k f s y-iteratedFDerivWithin ℝ k f s x‖≤H*‖y-x‖^alpha) :
    ∀t∈uIcc (0:ℝ) b,
      |iteratedDerivWithin (k-w.length) (along (axes s w f) a (basis axis)) (uIcc (0:ℝ) b) t-
        iteratedDerivWithin (k-w.length) (along (axes s w f) a (basis axis)) (uIcc (0:ℝ) b) 0|≤H*|t-0|^alpha := by
  intro t ht
  have he (u : ℝ) (hu : u∈uIcc (0:ℝ) b) := line_derivatives hs hf (w.map basis)
    (by simpa using (Nat.sub_add_cancel hw).le) a (basis axis) b hb inside hu
  have hd := axes_difference hs hf (List.replicate (k-w.length) axis++w)
    (by simp [Nat.sub_add_cancel hw]) (inside 0 left_mem_uIcc) (inside t ht)
  have hn : ‖a+t • basis axis-a‖≤|t| := by
    simpa using MathCan.WordTransport.step_norm axis 1 t |t| (by norm_num) le_rfl
  have hp := Real.rpow_le_rpow (norm_nonneg (a+t • basis axis-a)) hn ha
  have htensor := holder a (by simpa using inside 0 left_mem_uIcc) _ (inside t ht)
  simp only [axes,List.map_append,List.map_replicate,zero_smul,add_zero] at hd he ⊢
  rw [he t ht,he 0 left_mem_uIcc]
  simp only [zero_smul,add_zero,sub_zero]
  apply hd.trans
  convert htensor.trans (mul_le_mul_of_nonneg_left hp hH) using 1
  rw [show (List.replicate (k-w.length) axis++w).length=k by simp [Nat.sub_add_cancel hw]]

theorem axis_remainder {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (w : List (Fin d)) (hw : w.length≤k)
    (a : Space d) (axis : Fin d) (b H alpha : ℝ) (hb : b≠0) (hH : 0≤H) (ha : 0≤alpha)
    (inside : ∀t∈uIcc (0:ℝ) b,a+t • basis axis∈s)
    (holder : ∀x∈s,∀y∈s,
      ‖iteratedFDerivWithin ℝ k f s y-iteratedFDerivWithin ℝ k f s x‖≤H*‖y-x‖^alpha) :
    |along (axes s w f) a (basis axis) b-
      taylorWithinEval (along (axes s w f) a (basis axis)) (k-w.length) (uIcc (0:ℝ) b) 0 b|≤
      H*|b|^(((k-w.length:ℕ):ℝ)+alpha)/(Nat.factorial (k-w.length):ℝ) := by
  have hd:=axis_line_holder hs hf w hw a axis b H alpha hb hH ha inside holder
  have hg : ContDiffOn ℝ (k-w.length:ℕ) (axes s w f) s :=
    dir_smooth hs _ (by simpa [List.length_map,Nat.sub_add_cancel hw] using hf)
  have hl:=line_smooth hg a (basis axis) b inside
  generalize hm : k-w.length=m at *
  cases m with
  | zero =>
    have h := hd b right_mem_uIcc
    simpa [along] using h
  | succ m =>
    simpa only [sub_zero] using MathCan.SmoothTaylor.holder_remainder_bound hH ha hl hd

theorem values_bound {d k : ℕ} (s : Set (Space d)) (f : Space d→ℝ)
    (mu M : ℝ) (a : Space d) (hmu : 0≤mu) (hmu1 : mu≤1) (hM : 0≤M)
    (bound : ∀r,r≤k → ‖iteratedFDerivWithin ℝ r f s a‖≤M)
    (j : Fin (MathCan.WordTransport.size d k)) : |values s mu f a j|≤M := by
  obtain ⟨i,hi⟩:=(Fintype.equivFin (MathCan.WordTransport.Index d k)).surjective j
  rw [← hi,value_label]
  have hb:=component_bound (iteratedFDerivWithin ℝ i.1.val f s a) i.2
  have hfac : (1:ℝ)≤(Nat.factorial i.1.val:ℝ) := by exact_mod_cast Nat.factorial_pos i.1.val
  have hp : mu^i.1.val≤1 := pow_le_one₀ hmu hmu1
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤mu^i.1.val/(Nat.factorial i.1.val:ℝ))]
  have hscl : mu^i.1.val/(Nat.factorial i.1.val:ℝ)≤1 :=
    (div_le_self (pow_nonneg hmu _) hfac).trans hp
  exact (mul_le_mul_of_nonneg_left (hb.trans (bound i.1.val (by omega))) (by positivity)).trans
    (mul_le_of_le_one_left hM hscl)

theorem matrix_residual {d k : ℕ} {s : Set (Space d)} (hs : UniqueDiffOn ℝ s)
    {f : Space d→ℝ} (hf : ContDiffOn ℝ k f s) (a : Space d) (axis : Fin d)
    (mu q D H alpha tau : ℝ) (hmu : 0<mu) (hD : 1≤D) (hH : 0≤H)
    (ha : 0≤alpha) (htau : 0<tau) (hq : |q|≤D) (scale : mu^((k:ℝ)+alpha)≤2*tau)
    (inside : ∀t∈uIcc (0:ℝ) (mu*q),a+t • basis axis∈s)
    (holder : ∀x∈s,∀y∈s,
      ‖iteratedFDerivWithin ℝ k f s y-iteratedFDerivWithin ℝ k f s x‖≤H*‖y-x‖^alpha)
    (beta : Fin (MathCan.WordTransport.size d k)) :
    |values s mu f (a+(mu*q) • basis axis) beta-
      MathCan.WordTransport.row axis q (values s mu f a) beta|≤(2*H*D^((k:ℝ)+alpha))*tau := by
  have ha0 : a∈s := by simpa using inside 0 left_mem_uIcc
  have ha1 : a+(mu*q) • basis axis∈s := inside (mu*q) right_mem_uIcc
  by_cases hb : mu*q=0
  · have hq0 : q=0 := (mul_eq_zero.mp hb).resolve_left hmu.ne'
    rw [hb,zero_smul,add_zero,hq0,row_zero hs hf mu ha0,sub_self,abs_zero]
    positivity
  · let w:=MathCan.WordTransport.word beta
    let m:=k-w.length
    have hw : w.length≤k := MathCan.WordTransport.word_length beta
    have hr := axis_remainder hs hf w hw a axis (mu*q) H alpha hb hH ha inside holder
    have hp := Real.rpow_le_rpow (abs_nonneg (mu*q))
      (show |mu*q|≤mu*D by rw [abs_mul,abs_of_pos hmu]; exact mul_le_mul_of_nonneg_left hq hmu.le)
      (show 0≤(m:ℝ)+alpha by positivity)
    have hn : 0≤mu^w.length/(Nat.factorial w.length:ℝ) := by positivity
    have hfac : (0:ℝ)<(Nat.factorial w.length:ℝ)*(Nat.factorial m:ℝ) := by positivity
    have he : (w.length:ℝ)+((m:ℝ)+alpha)=(k:ℝ)+alpha := by
      have hm : w.length+m=k := by dsimp [m]; omega
      have hc : (w.length:ℝ)+(m:ℝ)=(k:ℝ) := by exact_mod_cast hm
      linarith
    have hbound := mul_le_mul_of_nonneg_left scale (show 0≤H*D^((m:ℝ)+alpha) by positivity)
    rw [values_axes hs hf mu ha1,row_compatibility hs hf mu ha0,
      axis_line_polynomial hs hf mu a axis q hb inside]
    rw [← mul_sub,abs_mul,abs_of_nonneg hn]
    have hraw : (mu^w.length/(Nat.factorial w.length:ℝ))*
        |axes s w f (a+(mu*q) • basis axis)-
          taylorWithinEval (along (axes s w f) a (basis axis)) m (uIcc (0:ℝ) (mu*q)) 0 (mu*q)|≤
        (2*H*D^((m:ℝ)+alpha)/((Nat.factorial w.length:ℝ)*(Nat.factorial m:ℝ)))*tau := by
      calc
        _ ≤ (mu^w.length/(Nat.factorial w.length:ℝ))*(H*|mu*q|^((m:ℝ)+alpha)/(Nat.factorial m:ℝ)) :=
          mul_le_mul_of_nonneg_left hr hn
        _ ≤ (mu^w.length/(Nat.factorial w.length:ℝ))*(H*(mu*D)^((m:ℝ)+alpha)/(Nat.factorial m:ℝ)) := by gcongr
        _ = H*D^((m:ℝ)+alpha)*mu^((k:ℝ)+alpha)/((Nat.factorial w.length:ℝ)*(Nat.factorial m:ℝ)) := by
          rw [Real.mul_rpow hmu.le (by linarith),← he]
          rw [Real.rpow_add_of_nonneg hmu.le (Nat.cast_nonneg w.length) (by positivity : 0≤(m:ℝ)+alpha)]
          rw [Real.rpow_natCast]
          ring
        _ ≤ _ := by
          apply (div_le_div_of_nonneg_right hbound hfac.le).trans
          apply le_of_eq; ring
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (MathCan.SharpJet.uniform_component_budget w.length m k D H alpha hD hH (by dsimp [m]; omega)) htau.le)

theorem evaluation_error {d k : ℕ} (v u : Fin (MathCan.WordTransport.size d k)→ℝ)
    (h : Space d) (D epsilon : ℝ) (hD : 1≤D) (hh : ‖h‖≤D)
    (error : ∀j,|v j-u j|≤epsilon) :
    |MathCan.WordTransport.evaluate v h-MathCan.WordTransport.evaluate u h|≤
      (MathCan.WordTransport.size d k:ℝ)*D^k*epsilon := by
  classical
  unfold MathCan.WordTransport.evaluate
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑i:MathCan.WordTransport.Index d k,
        |(v (Fintype.equivFin _ i)-u (Fintype.equivFin _ i))*∏j,h (i.2 j)| := by
      simpa only [sub_mul] using Finset.abs_sum_le_sum_abs
        (fun i:MathCan.WordTransport.Index d k=>v (Fintype.equivFin _ i)*(∏j,h (i.2 j))-
          u (Fintype.equivFin _ i)*(∏j,h (i.2 j))) Finset.univ
    _ ≤ ∑_i:MathCan.WordTransport.Index d k,D^k*epsilon := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,Finset.abs_prod]
      have hc : ∀j:Fin d,|h j|≤D := fun j=>
        (show |h j|≤‖h‖ by simpa using norm_le_pi_norm h j).trans hh
      have hp : (∏j,|h (i.2 j)|)≤D^k := by
        apply (Finset.prod_le_prod (fun j _=>abs_nonneg _) (fun j _=>hc (i.2 j))).trans
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        exact MathCan.CommonGateBound.power_mono_exponent D hD i.1.val k (by omega)
      simpa [mul_comm] using mul_le_mul (error (Fintype.equivFin _ i)) hp (Finset.prod_nonneg (fun j _=>abs_nonneg _))
        (abs_nonneg _ |>.trans (error (Fintype.equivFin _ i)))
    _ = _ := by simp [MathCan.WordTransport.size]; ring

end MathCan.CubeTaylor

namespace MathCan.CubeAnchors
open Set MathCan.MultivariateTaylor MathCan.CubeTaylor MathCan.SpatialScalar MathCan.SpatialRouting
set_option autoImplicit false

def unrank (K : ℕ) : (d : ℕ)→ℕ→Fin d→ℕ
  | 0, _ => Fin.elim0
  | d+1, r => Fin.cons (r/(K^d)) (unrank K d
      (if (r/(K^d))%2=0 then r%(K^d) else K^d-1-r%(K^d)))

theorem digit_div (B i r : ℕ) (hB : 0<B) (hr : r<B) : (i*B+r)/B=i := by
  rw [Nat.mul_comm i B,Nat.mul_add_div hB,Nat.div_eq_of_lt hr,Nat.add_zero]

theorem digit_mod (B i r : ℕ) (hr : r<B) : (i*B+r)%B=r := by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hr]

theorem unrank_bound (K d r : ℕ) (hK : 0<K) (hr : r<K^d) : ∀j,unrank K d r j<K := by
  induction d generalizing r with
  | zero => intro j; exact Fin.elim0 j
  | succ d ih =>
    have hB : 0<K^d := Nat.pow_pos hK
    have hq : r/(K^d)<K := (Nat.div_lt_iff_lt_mul hB).2 (by simpa [Nat.pow_succ,Nat.mul_comm] using hr)
    have hm : r%(K^d)<K^d := Nat.mod_lt _ hB
    intro j
    cases j using Fin.cases
    · exact hq
    · apply ih
      split
      · exact hm
      · exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hB (by decide : 0<1))

theorem unrank_rank (K d : ℕ) (hK : 0<K) (g : Fin d→ℕ) (hg : ∀j,g j<K) :
    unrank K d (snakeRank K (List.ofFn g))=g := by
  induction d with
  | zero => funext j; exact Fin.elim0 j
  | succ d ih =>
    let tail := fun i:Fin d=>g i.succ
    let r := snakeRank K (List.ofFn tail)
    have hB : 0<K^d := Nat.pow_pos hK
    have hr : r<K^d := by
      have hh:=snake_rank_bound K hK (List.ofFn tail) (by
        intro i hi
        obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
        exact hg _)
      simpa only [List.length_ofFn] using hh
    have ht : unrank K d r=tail := ih tail (fun j=>hg j.succ)
    rw [List.ofFn_succ]
    simp only [snakeRank,List.length_ofFn]
    by_cases he : g 0%2=0
    · rw [if_pos he]
      change Fin.cons ((g 0*K^d+r)/K^d) (unrank K d
        (if ((g 0*K^d+r)/K^d)%2=0 then (g 0*K^d+r)%K^d else K^d-1-(g 0*K^d+r)%K^d))=g
      rw [digit_div _ _ _ hB hr,digit_mod _ _ _ hr,if_pos he,ht]
      exact Fin.cons_self_tail g
    · have hr' : K^d-1-r<K^d := by omega
      rw [if_neg he]
      change Fin.cons ((g 0*K^d+(K^d-1-r))/K^d) (unrank K d
        (if ((g 0*K^d+(K^d-1-r))/K^d)%2=0 then (g 0*K^d+(K^d-1-r))%K^d else K^d-1-(g 0*K^d+(K^d-1-r))%K^d))=g
      rw [digit_div _ _ _ hB hr',digit_mod _ _ _ hr',if_neg he,show K^d-1-(K^d-1-r)=r by omega,ht]
      exact Fin.cons_self_tail g

noncomputable def anchor {d : ℕ} (h : ℝ) (theta : Space d) (coarse : Fin d→ℕ)
    (K : ℕ) (g : Fin d→ℕ) : Space d :=
  fun j=>clip 1 (h*((coarse j*K+g j:ℕ)+theta j-1))

theorem anchor_in_cube {d : ℕ} (h : ℝ) (theta : Space d) (coarse : Fin d→ℕ)
    (K : ℕ) (g : Fin d→ℕ) : anchor h theta coarse K g∈cube d :=
  fun _=>clip_range _ _ (by norm_num)

theorem clip_rescale (h z : ℝ) (hh : 0<h) : h*clip (h⁻¹) z=clip 1 (h*z) := by
  have he (v : ℝ) : h*relu v=relu (h*v) := by
    by_cases hv : v<0
    · simp [relu,hv,mul_neg_of_pos_of_neg hh hv]
    · simp [relu,hv,not_lt.mpr (mul_nonneg hh.le (le_of_not_gt hv))]
  unfold clip
  rw [mul_sub,he,he,mul_sub,mul_inv_cancel₀ hh.ne']

theorem safe_coverage {d : ℕ} (h delta : ℝ) (hh : 0<h) (hd : 0<delta)
    (x theta : Space d) (coarse fine : Fin d→ℕ) (K : ℕ) (hx : x∈cube d)
    (safe : ∀j,safeCell delta (h⁻¹*x j+1-theta j) (coarse j*K+fine j)) :
    ‖x-anchor h theta coarse K fine‖≤h := by
  apply (pi_norm_le_iff_of_nonneg hh.le).2
  intro j
  have hp : 0≤h⁻¹*x j ∧ h⁻¹*x j≤h⁻¹ :=
    ⟨mul_nonneg (inv_nonneg.mpr hh.le) (hx j).1,by simpa using mul_le_mul_of_nonneg_left (hx j).2 (inv_nonneg.mpr hh.le)⟩
  have hb := boundary_anchor (h⁻¹) (h⁻¹*x j) (theta j) delta (coarse j*K+fine j) hp hd (safe j)
  have hs := clip_rescale h ((coarse j*K+fine j:ℕ)+theta j-1) hh
  have hi : h*h⁻¹=1 := mul_inv_cancel₀ hh.ne'
  have hlo := mul_nonneg hh.le hb.1
  have hup := mul_le_mul_of_nonneg_left hb.2 hh.le
  rw [mul_sub,← mul_assoc,hi,one_mul] at hlo hup
  change |x j-clip 1 (h*((coarse j*K+fine j:ℕ)+theta j-1))|≤h
  rw [← hs,abs_of_nonneg hlo]
  simpa only [mul_one] using hup

theorem selected_anchor {d : ℕ} (K : ℕ) (hK : 0<K) (h : ℝ) (theta : Space d)
    (coarse fine : Fin d→ℕ) (hf : ∀j,fine j<K) :
    anchor h theta coarse K (unrank K d (snakeRank K (List.ofFn fine)))=
      anchor h theta coarse K fine := by rw [unrank_rank K d hK fine hf]

theorem selected_coverage {d : ℕ} (K : ℕ) (hK : 0<K) (h delta : ℝ) (hh : 0<h) (hd : 0<delta)
    (x theta : Space d) (coarse fine : Fin d→ℕ) (hf : ∀j,fine j<K) (hx : x∈cube d)
    (safe : ∀j,safeCell delta (h⁻¹*x j+1-theta j) (coarse j*K+fine j)) :
    ‖x-anchor h theta coarse K (unrank K d (snakeRank K (List.ofFn fine)))‖≤h := by
  rw [selected_anchor K hK h theta coarse fine hf]
  exact safe_coverage h delta hh hd x theta coarse fine K hx safe

end MathCan.CubeAnchors

namespace MathCan.CubeCapture
open Set MathCan.MultivariateTaylor MathCan.CubeTaylor MathCan.WordCapture
open MathCan.SpatialNormalized MathCan.SpatialRouting MathCan.CommonGateBound
set_option autoImplicit false

theorem axis_segment {d : ℕ} (a : Space d) (axis : Fin d) (b : ℝ)
    (ha : a∈cube d) (hb : a+b • basis axis∈cube d) :
    ∀t∈uIcc (0:ℝ) b,a+t • basis axis∈cube d := by
  intro t ht j
  by_cases hj : j=axis
  · subst j
    have ha':=ha axis
    have hb':=hb axis
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,basis,Pi.single_eq_same,mul_one] at hb' ⊢
    rcases le_total (0:ℝ) b with h | h
    · rw [uIcc_of_le h] at ht
      constructor <;> linarith [ht.1,ht.2,ha'.1,hb'.2]
    · rw [uIcc_of_ge h] at ht
      constructor <;> linarith [ht.1,ht.2,ha'.2,hb'.1]
  · simpa [basis,Pi.single_apply,hj] using ha j

noncomputable def targets {d k D : ℕ} (mu : ℝ) (f : Space d→ℝ)
    (tags : List (Tag d D)) (a : Space d) (i : ℕ) : Fin (MathCan.WordTransport.size d k)→ℝ :=
  CubeTaylor.values (cube d) mu f (anchors mu tags a i)

theorem targets_residuals {d k D : ℕ} {f : Space d→ℝ} (hf : ContDiffOn ℝ k f (cube d))
    (hD : 1≤D) (mu H alpha tau : ℝ) (hmu : 0<mu) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau)
    (scale : mu^((k:ℝ)+alpha)≤2*tau)
    (holder : ∀x∈cube d,∀y∈cube d,
      ‖iteratedFDerivWithin ℝ k f (cube d) y-iteratedFDerivWithin ℝ k f (cube d) x‖≤H*‖y-x‖^alpha)
    (tags : List (Tag d D)) (a : Space d)
    (inside : ∀i,i≤tags.length → anchors mu tags a i∈cube d) :
    Residuals tau (2*H*(D:ℝ)^((k:ℝ)+alpha)) tags (targets (k:=k) mu f tags a) := by
  induction tags generalizing a with
  | nil => trivial
  | cons tag tail ih =>
    have ha0 : a∈cube d := by simpa [anchors] using inside 0 (by simp)
    have ha1 : a+(mu*amount tag) • basis (axis tag)∈cube d := by
      simpa [anchors] using inside 1 (by simp)
    constructor
    · intro beta
      simpa only [targets,anchors,predict] using CubeTaylor.matrix_residual (cube_uniqueDiff d) hf a
        (axis tag) mu (amount tag) (D:ℝ) H alpha tau hmu (by exact_mod_cast hD) hH ha htau
        (amount_bound tag) scale (axis_segment a (axis tag) (mu*amount tag) ha0 ha1) holder beta
    · apply ih
      intro i hi
      simpa only [anchors] using inside (i+1) (by simp only [List.length_cons]; omega)

theorem normalized_approximation {d n : ℕ} {f : Space d→ℝ} (hf : ContDiffOn ℝ (n+1) f (cube d))
    (mu D H alpha tau rho : ℝ) (hmu : 0<mu) (hD : 1≤D) (hH : 0≤H) (ha : 0≤alpha)
    (htau : 0<tau) (a x : Space d) (ha0 : a∈cube d) (hx : x∈cube d)
    (hdist : ‖x-a‖≤rho) (hrho : rho≤mu*D)
    (holder : ∀y∈cube d,∀z∈cube d,
      ‖iteratedFDerivWithin ℝ (n+1) f (cube d) z-iteratedFDerivWithin ℝ (n+1) f (cube d) y‖≤H*‖z-y‖^alpha)
    (v : Fin (MathCan.WordTransport.size d (n+1))→ℝ)
    (accurate : ∀j,|v j-CubeTaylor.values (cube d) mu f a j|≤tau/2) :
    |f x-MathCan.WordTransport.evaluate v (mu⁻¹ • (x-a))|≤
      H*rho^(((n+1:ℕ):ℝ)+alpha)/(Nat.factorial (n+1):ℝ)+
        (MathCan.WordTransport.size d (n+1):ℝ)*D^(n+1)*(tau/2) := by
  have hh : ‖mu⁻¹ • (x-a)‖≤D := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hmu)]
    calc
      _ ≤ mu⁻¹*(mu*D) := mul_le_mul_of_nonneg_left (hdist.trans hrho) (inv_nonneg.mpr hmu.le)
      _ = D := by rw [← mul_assoc,inv_mul_cancel₀ hmu.ne',one_mul]
  have ht:=CubeTaylor.holder_remainder (cube_uniqueDiff d) hf a (x-a) H alpha hH ha
    (fun t ht=>cube_segment ha0 hx ht) (fun t ht=>holder a ha0 _ (cube_segment ha0 hx ht))
  simp only [add_sub_cancel] at ht
  have hp:=Real.rpow_le_rpow (norm_nonneg (x-a)) hdist (show 0≤((n+1:ℕ):ℝ)+alpha by positivity)
  have hb:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hH) (Nat.cast_nonneg (Nat.factorial (n+1)))
  have heval:=CubeTaylor.evaluation_error v (CubeTaylor.values (cube d) mu f a) (mu⁻¹ • (x-a)) D (tau/2) hD hh accurate
  rw [CubeTaylor.evaluation_values (cube d) f mu hmu,abs_sub_comm] at heval
  exact (abs_sub_le (f x) (polynomial (cube d) f (n+1) a (x-a))
    (MathCan.WordTransport.evaluate v (mu⁻¹ • (x-a)))).trans (add_le_add (ht.trans hb) heval)

theorem decoded_approximation {d n D : ℕ} {f : Space d→ℝ} (hf : ContDiffOn ℝ (n+1) f (cube d))
    (hD : 1≤D) (spatialN K p a N : ℕ) (hK : 0<K) (hTags : tagCount d D<2^p)
    (hwidth : 2*N<2^a) (delta mu M H alpha tau rho : ℝ)
    (hdelta : 0<delta) (hmu : 0<mu) (hmu1 : mu≤1) (hM : 0≤M) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau)
    (scale : mu^(((n+1:ℕ):ℝ)+alpha)≤2*tau)
    (hN : 2*H*(D:ℝ)^(((n+1:ℕ):ℝ)+alpha)+commonBudget (n+1) D/2+1/2≤(N:ℝ))
    (holder : ∀y∈cube d,∀z∈cube d,
      ‖iteratedFDerivWithin ℝ (n+1) f (cube d) z-iteratedFDerivWithin ℝ (n+1) f (cube d) y‖≤H*‖z-y‖^alpha)
    (sites : List (Site ℝ)) (safe : validSites spatialN K delta sites)
    (tags : List (Tag d D)) (alignment : tags.length+1=K^sites.length) (a0 x : Space d)
    (inside : ∀i,i≤tags.length → anchors mu tags a0 i∈cube d) (hx : x∈cube d)
    (bound : ∀y∈cube d,∀r,r≤n+1 → ‖iteratedFDerivWithin ℝ r f (cube d) y‖≤M)
    (hdist : ‖x-anchors mu tags a0 (snakeRank K (sites.map Site.fine))‖≤rho) (hrho : rho≤mu*(D:ℝ)) :
    |f x-MathCan.WordTransport.evaluate
      (captured spatialN K p a N delta M tau sites tags (targets (k:=n+1) mu f tags a0))
      (mu⁻¹ • (x-anchors mu tags a0 (snakeRank K (sites.map Site.fine))))|≤
      H*rho^(((n+1:ℕ):ℝ)+alpha)/(Nat.factorial (n+1):ℝ)+
        (MathCan.WordTransport.size d (n+1):ℝ)*(D:ℝ)^(n+1)*(tau/2) := by
  have hb : ∀i,i≤tags.length → ∀j,-M≤targets (k:=n+1) mu f tags a0 i j ∧
      targets (k:=n+1) mu f tags a0 i j≤M := by
    intro i hi j
    exact abs_le.mp (CubeTaylor.values_bound (cube d) f mu M _ hmu.le hmu1 hM (bound _ (inside i hi)) j)
  have hr:=targets_residuals hf hD mu H alpha tau hmu hH ha htau scale holder tags a0 inside
  have hc:=captured_accuracy hD spatialN K p a N hK hTags hwidth delta M tau
    (2*H*(D:ℝ)^(((n+1:ℕ):ℝ)+alpha)) hdelta hM htau hN sites safe tags alignment
    (targets (k:=n+1) mu f tags a0) hr hb
  have hidx : snakeRank K (sites.map Site.fine)≤tags.length := by
    have h:=snake_rank_bound K hK (sites.map Site.fine) (by
      intro j hj
      obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hj
      exact (safe s hs).2.1)
    simp only [List.length_map] at h
    omega
  exact normalized_approximation hf mu D H alpha tau rho hmu (by exact_mod_cast hD) hH ha htau _ x
    (inside _ hidx) hx hdist hrho holder _ hc

end MathCan.CubeCapture

namespace MathCan.CubeWalk
open Set MathCan.MultivariateTaylor MathCan.CubeTaylor MathCan.CubeAnchors MathCan.WordCapture
set_option autoImplicit false

def Adjacent {d : ℕ} (g h : Fin d→ℕ) : Prop :=
  ∃j,(g j+1=h j ∨ h j+1=g j) ∧ ∀l,l≠j → g l=h l

theorem adjacent_symm {d : ℕ} {g h : Fin d→ℕ} (hh : Adjacent g h) : Adjacent h g := by
  obtain ⟨j,hj,hs⟩:=hh
  exact ⟨j,hj.symm,fun l hl=>(hs l hl).symm⟩

theorem adjacent_cons {d : ℕ} {g h : Fin d→ℕ} (i : ℕ) (hh : Adjacent g h) :
    Adjacent (Fin.cons i g) (Fin.cons i h) := by
  obtain ⟨j,hj,hs⟩:=hh
  refine ⟨j.succ,by simpa using hj,?_⟩
  intro l hl
  cases l using Fin.cases
  · rfl
  · apply hs
    intro he
    exact hl (congrArg Fin.succ he)

theorem adjacent_head {d : ℕ} (i : ℕ) (g : Fin d→ℕ) :
    Adjacent (Fin.cons i g) (Fin.cons (i+1) g) := by
  refine ⟨0,Or.inl rfl,?_⟩
  intro j hj
  cases j using Fin.cases
  · exact False.elim (hj rfl)
  · rfl

theorem unrank_step (K d r : ℕ) (hK : 0<K) (hr : r+1<K^d) :
    Adjacent (unrank K d r) (unrank K d (r+1)) := by
  induction d generalizing r with
  | zero => simp at hr
  | succ d ih =>
    let B:=K^d
    let q:=r/B
    let u:=r%B
    have hB : 0<B := Nat.pow_pos hK
    have hu : u<B := Nat.mod_lt r hB
    have he : q*B+u=r := by simpa [q,u,Nat.mul_comm] using Nat.div_add_mod r B
    have hc : unrank K (d+1) r=Fin.cons q (unrank K d (if q%2=0 then u else B-1-u)) := rfl
    rw [hc]
    by_cases carry : u+1<B
    · have hn : r+1=q*B+(u+1) := by omega
      have hd : (r+1)/B=q := by rw [hn,digit_div B q (u+1) hB carry]
      have hm : (r+1)%B=u+1 := by rw [hn,digit_mod B q (u+1) carry]
      change Adjacent _ (Fin.cons ((r+1)/B) (unrank K d
        (if ((r+1)/B)%2=0 then (r+1)%B else B-1-(r+1)%B)))
      rw [hd,hm]
      by_cases hq : q%2=0
      · simp only [if_pos hq]
        exact adjacent_cons q (ih u carry)
      · simp only [if_neg hq]
        have hv : B-1-(u+1)+1=B-1-u := by omega
        have hvb : B-1-(u+1)+1<B := by omega
        have hh:=adjacent_symm (ih (B-1-(u+1)) hvb)
        rw [hv] at hh
        exact adjacent_cons q hh
    · have hu' : u+1=B := by omega
      have hn : r+1=(q+1)*B+0 := by rw [Nat.add_mul]; omega
      have hd : (r+1)/B=q+1 := by rw [hn,digit_div B (q+1) 0 hB hB]
      have hm : (r+1)%B=0 := by rw [hn,digit_mod B (q+1) 0 hB]
      change Adjacent _ (Fin.cons ((r+1)/B) (unrank K d
        (if ((r+1)/B)%2=0 then (r+1)%B else B-1-(r+1)%B)))
      rw [hd,hm]
      by_cases hq : q%2=0
      · have hq' : (q+1)%2≠0 := by omega
        rw [if_pos hq,if_neg hq',Nat.sub_zero,show u=B-1 by omega]
        exact adjacent_head q _
      · have hq' : (q+1)%2=0 := by omega
        rw [if_neg hq,if_pos hq',show B-1-u=0 by omega]
        exact adjacent_head q _

noncomputable def lattice {d : ℕ} (cap D : ℕ) (shift : Fin d→ℤ)
    (coarse : Fin d→ℕ) (K : ℕ) (g : Fin d→ℕ) (j : Fin d) : ℤ :=
  MathCan.SpatialInterface.anchor cap D (shift j) (coarse j*K+g j)

noncomputable def point {d : ℕ} (cap D : ℕ) (mu : ℝ) (shift : Fin d→ℤ)
    (coarse : Fin d→ℕ) (K : ℕ) (g : Fin d→ℕ) : Space d :=
  fun j=>mu*(lattice cap D shift coarse K g j:ℝ)

theorem point_in_cube {d : ℕ} (cap D : ℕ) (mu : ℝ) (hmu : 0≤mu)
    (hcap : mu*(cap:ℝ)≤1) (shift : Fin d→ℤ) (coarse : Fin d→ℕ) (K : ℕ) (g : Fin d→ℕ) :
    point cap D mu shift coarse K g∈cube d := by
  intro j
  have hr:=MathCan.SpatialInterface.clamp_range (cap:ℤ)
    ((D:ℤ)*(coarse j*K+g j)+(shift j)-(D:ℤ)) (Int.natCast_nonneg cap)
  constructor
  · exact mul_nonneg hmu (by exact_mod_cast hr.1)
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hr.2) hmu).trans hcap

theorem lattice_step {d : ℕ} (cap D K : ℕ) (shift : Fin d→ℤ) (coarse : Fin d→ℕ)
    (g h : Fin d→ℕ) (axis : Fin d) (forward : g axis+1=h axis) :
    0≤lattice cap D shift coarse K h axis-lattice cap D shift coarse K g axis ∧
    lattice cap D shift coarse K h axis-lattice cap D shift coarse K g axis≤(D:ℤ) := by
  have hn : coarse axis*K+h axis=coarse axis*K+g axis+1 := by omega
  have he : (coarse axis*K+h axis:ℤ)=(coarse axis*K+g axis:ℤ)+1 := by exact_mod_cast hn
  unfold lattice
  rw [he]
  exact MathCan.SpatialInterface.anchor_step cap D (shift axis) _ (Int.natCast_nonneg cap) (Int.natCast_nonneg D)

theorem delta_motion {d D : ℕ} (axis : Fin d) (z : ℤ) (hz : -(D:ℤ)≤z ∧ z≤(D:ℤ)) :
    ∃tag:Tag d D,WordCapture.axis tag=axis ∧ amount tag=(z:ℝ) := by
  have habs : z.natAbs≤D := by
    by_cases h : 0≤z
    · have he:=Int.natAbs_of_nonneg h
      omega
    · have he:=Int.ofNat_natAbs_of_nonpos (by omega : z≤0)
      omega
  let m : Motion d D := ⟨axis,decide (z<0),⟨z.natAbs,by omega⟩⟩
  refine ⟨Fintype.equivFin (Motion d D) m,?_,?_⟩
  · simp [WordCapture.axis,motion,m]
  · simp only [amount,motion,Equiv.symm_apply_apply,m,MathCan.TaylorTransport.signedStep]
    by_cases h : z<0
    · have he:=congrArg (fun z:ℤ=>(z:ℝ)) (Int.eq_neg_natAbs_of_nonpos (by omega : z≤0))
      simpa [h] using he.symm
    · have he:=congrArg (fun z:ℤ=>(z:ℝ)) (Int.natAbs_of_nonneg (by omega : 0≤z))
      simpa only [h,decide_false,Bool.false_eq_true,if_false,Int.cast_natCast] using he

theorem adjacent_motion {d : ℕ} (cap D K : ℕ) (mu : ℝ) (shift : Fin d→ℤ) (coarse : Fin d→ℕ)
    (g h : Fin d→ℕ) (adj : Adjacent g h) :
    ∃tag:Tag d D,point cap D mu shift coarse K h=
      point cap D mu shift coarse K g+(mu*amount tag) • basis (WordCapture.axis tag) := by
  obtain ⟨axis,step,same⟩:=adj
  let z := lattice cap D shift coarse K h axis-lattice cap D shift coarse K g axis
  have hz : -(D:ℤ)≤z ∧ z≤(D:ℤ) := by
    rcases step with he | he
    · have hh:=lattice_step cap D K shift coarse g h axis he
      dsimp [z]; omega
    · have hh:=lattice_step cap D K shift coarse h g axis he
      dsimp [z]; omega
  obtain ⟨tag,haxis,hamount⟩:=delta_motion axis z hz
  refine ⟨tag,?_⟩
  rw [haxis,hamount]
  ext j
  by_cases hj : j=axis
  · subst j
    simp only [point,Pi.add_apply,Pi.smul_apply,basis,Pi.single_eq_same,smul_eq_mul,mul_one,z,Int.cast_sub]
    ring
  · have hl : lattice cap D shift coarse K h j=lattice cap D shift coarse K g j := by
      unfold lattice
      rw [same j hj]
    simp [point,basis,Pi.single_apply,hj,hl]

theorem clamp_cast (cap : ℕ) (z : ℤ) :
    (MathCan.SpatialInterface.clamp cap z:ℝ)=MathCan.SpatialScalar.clip (cap:ℝ) (z:ℝ) := by
  have hc : (0:ℝ)≤cap := Nat.cast_nonneg cap
  by_cases hz : (z:ℝ)<0
  · have hz' : z<0 := by exact_mod_cast hz
    simp [MathCan.SpatialInterface.clamp,hz',MathCan.SpatialScalar.clip,MathCan.SpatialScalar.relu,
      hz,show (z:ℝ)-(cap:ℝ)<0 by linarith]
  · have hz' : ¬z<0 := by exact_mod_cast hz
    by_cases hcz : (cap:ℝ)<(z:ℝ)
    · have hcz' : (cap:ℤ)<z := by exact_mod_cast hcz
      simp [MathCan.SpatialInterface.clamp,hz',hcz',MathCan.SpatialScalar.clip,MathCan.SpatialScalar.relu,
        hz,show ¬(z:ℝ)-(cap:ℝ)<0 by linarith]
    · have hcz' : ¬(cap:ℤ)<z := by exact_mod_cast hcz
      rw [MathCan.SpatialInterface.clamp,if_neg hz',if_neg hcz']
      exact (MathCan.SpatialScalar.clip_identity _ _ ⟨le_of_not_gt hz,le_of_not_gt hcz⟩).symm

theorem point_anchor {d : ℕ} (cap D K : ℕ) (hD : 0<D) (mu : ℝ) (hmu : 0<mu)
    (hcap : mu*(cap:ℝ)=1) (shift : Fin d→ℤ) (coarse g : Fin d→ℕ) :
    point cap D mu shift coarse K g=
      anchor (mu*(D:ℝ)) (fun j=>(shift j:ℝ)/(D:ℝ)) coarse K g := by
  have hcap' : (cap:ℝ)=mu⁻¹ := by
    apply mul_left_cancel₀ hmu.ne'
    rw [hcap,mul_inv_cancel₀ hmu.ne']
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  ext j
  unfold point lattice MathCan.SpatialInterface.anchor
  rw [clamp_cast,hcap',clip_rescale mu _ hmu]
  unfold anchor
  congr 1
  push_cast
  field_simp
  <;> ring

noncomputable def edge {d : ℕ} (cap D K : ℕ) (hK : 0<K) (mu : ℝ)
    (shift : Fin d→ℤ) (coarse : Fin d→ℕ) (i : Fin (K^d-1)) : Tag d D :=
  Classical.choose (adjacent_motion cap D K mu shift coarse (unrank K d i.val) (unrank K d (i.val+1))
    (unrank_step K d i.val hK (by have:=i.isLt; have:=Nat.pow_pos hK (n:=d); omega)))

theorem edge_step {d : ℕ} (cap D K : ℕ) (hK : 0<K) (mu : ℝ)
    (shift : Fin d→ℤ) (coarse : Fin d→ℕ) (i : Fin (K^d-1)) :
    point cap D mu shift coarse K (unrank K d (i.val+1))=
      point cap D mu shift coarse K (unrank K d i.val)+
        (mu*amount (edge cap D K hK mu shift coarse i)) • basis (WordCapture.axis (edge cap D K hK mu shift coarse i)) :=
  Classical.choose_spec (adjacent_motion cap D K mu shift coarse (unrank K d i.val) (unrank K d (i.val+1))
    (unrank_step K d i.val hK (by have:=i.isLt; have:=Nat.pow_pos hK (n:=d); omega)))

noncomputable def schedule {d : ℕ} (cap D K : ℕ) (hK : 0<K) (mu : ℝ)
    (shift : Fin d→ℤ) (coarse : Fin d→ℕ) : List (Tag d D) :=
  List.ofFn (edge cap D K hK mu shift coarse)

theorem schedule_length {d : ℕ} (cap D K : ℕ) (hK : 0<K) (mu : ℝ)
    (shift : Fin d→ℤ) (coarse : Fin d→ℕ) : (schedule cap D K hK mu shift coarse).length+1=K^d := by
  simp only [schedule,List.length_ofFn]
  have:=Nat.pow_pos hK (n:=d)
  omega

theorem anchors_zero {d D : ℕ} (mu : ℝ) (tags : List (Tag d D)) (a : Space d) : anchors mu tags a 0=a := by
  cases tags <;> rfl

theorem anchors_succ {d D : ℕ} (mu : ℝ) (tags : List (Tag d D)) (a : Space d)
    (i : ℕ) (hi : i<tags.length) :
    anchors mu tags a (i+1)=anchors mu tags a i+
      (mu*amount tags[i]) • basis (WordCapture.axis tags[i]) := by
  induction tags generalizing i a with
  | nil => simp at hi
  | cons tag tail ih =>
    cases i with
    | zero => simp only [anchors,List.getElem_cons_zero,anchors_zero]
    | succ i =>
      simpa only [anchors,List.getElem_cons_succ] using ih (a+(mu*amount tag) • basis (WordCapture.axis tag)) i (by simpa using hi)

theorem schedule_anchors {d : ℕ} (cap D K : ℕ) (hK : 0<K) (mu : ℝ)
    (shift : Fin d→ℤ) (coarse : Fin d→ℕ) (i : ℕ) (hi : i<K^d) :
    anchors mu (schedule cap D K hK mu shift coarse)
      (point cap D mu shift coarse K (unrank K d 0)) i=
      point cap D mu shift coarse K (unrank K d i) := by
  induction i with
  | zero => exact anchors_zero _ _ _
  | succ i ih =>
    have hlen:=schedule_length cap D K hK mu shift coarse
    have hi' : i<(schedule cap D K hK mu shift coarse).length := by omega
    rw [anchors_succ mu _ _ i hi',ih (by omega)]
    have he:=edge_step cap D K hK mu shift coarse ⟨i,by simp only [schedule,List.length_ofFn] at hi'; exact hi'⟩
    simpa only [schedule,List.getElem_ofFn] using he.symm

end MathCan.CubeWalk

namespace MathCan.CubeSpatial
open Set MathCan.MultivariateTaylor MathCan.CubeTaylor MathCan.CubeAnchors MathCan.CubeWalk
open MathCan.WordCapture MathCan.SpatialNormalized MathCan.SpatialRouting MathCan.CommonGateBound
set_option autoImplicit false

noncomputable def querySites {d : ℕ} (h : ℝ) (theta : Space d) (coarse fine : Fin d→ℕ)
    (x : Space d) : List (Site ℝ) :=
  List.ofFn (fun j=>⟨coarse j,fine j,h⁻¹*x j+1-theta j⟩)

theorem query_fine {d : ℕ} (h : ℝ) (theta : Space d) (coarse fine : Fin d→ℕ) (x : Space d) :
    (querySites h theta coarse fine x).map Site.fine=List.ofFn fine := by
  simp only [querySites,List.map_ofFn]
  rfl

theorem query_valid {d : ℕ} (spatialN K : ℕ) (h delta : ℝ) (theta : Space d)
    (coarse fine : Fin d→ℕ) (x : Space d) (hc : ∀j,coarse j≤spatialN) (hf : ∀j,fine j<K)
    (safe : ∀j,MathCan.SpatialScalar.safeCell delta (h⁻¹*x j+1-theta j) (coarse j*K+fine j)) :
    validSites spatialN K delta (querySites h theta coarse fine x) := by
  intro s hs
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hs
  exact ⟨hc j,hf j,safe j⟩

theorem schedule_inside {d : ℕ} (cap D K : ℕ) (hK : 0<K) (mu : ℝ) (hmu : 0≤mu)
    (hcap : mu*(cap:ℝ)≤1) (shift : Fin d→ℤ) (coarse : Fin d→ℕ)
    (i : ℕ) (hi : i≤(schedule cap D K hK mu shift coarse).length) :
    anchors mu (schedule cap D K hK mu shift coarse)
      (point cap D mu shift coarse K (unrank K d 0)) i∈cube d := by
  have hlen:=schedule_length cap D K hK mu shift coarse
  rw [schedule_anchors cap D K hK mu shift coarse i (by omega)]
  exact point_in_cube cap D mu hmu hcap shift coarse K _

theorem schedule_selected {d : ℕ} (cap D K : ℕ) (hK : 0<K) (mu : ℝ)
    (shift : Fin d→ℤ) (coarse fine : Fin d→ℕ) (hf : ∀j,fine j<K) :
    anchors mu (schedule cap D K hK mu shift coarse)
      (point cap D mu shift coarse K (unrank K d 0)) (snakeRank K (List.ofFn fine))=
      point cap D mu shift coarse K fine := by
  have hi : snakeRank K (List.ofFn fine)<K^d := by
    have h:=snake_rank_bound K hK (List.ofFn fine) (by
      intro i hi
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
      exact hf j)
    simpa only [List.length_ofFn] using h
  rw [schedule_anchors cap D K hK mu shift coarse _ hi,unrank_rank K d hK fine hf]

theorem micro_scale_le_one (cap : ℕ) (mu : ℝ) (hmu : 0<mu) (hcap : mu*(cap:ℝ)=1) : mu≤1 := by
  have hc : 1≤cap := by
    by_contra h
    have hz : cap=0 := by omega
    simp [hz] at hcap
  have hc' : (1:ℝ)≤cap := by exact_mod_cast hc
  nlinarith [mul_le_mul_of_nonneg_left hc' hmu.le]

noncomputable def decoded {d k D : ℕ} (spatialN K p a N cap : ℕ) (hK : 0<K)
    (delta mu M tau : ℝ) (f : Space d→ℝ) (shift : Fin d→ℤ) (coarse fine : Fin d→ℕ) (x : Space d) :
    Fin (MathCan.WordTransport.size d k)→ℝ :=
  captured spatialN K p a N delta M tau
    (querySites (mu*(D:ℝ)) (fun j=>(shift j:ℝ)/(D:ℝ)) coarse fine x)
    (schedule cap D K hK mu shift coarse)
    (CubeCapture.targets (k:=k) mu f (schedule cap D K hK mu shift coarse)
      (point cap D mu shift coarse K (unrank K d 0)))

/-- The actual base-4 decoded spatial jet approximates a function intrinsically
smooth on the closed cube. The schedule, coverage and Taylor residuals are proved. -/
theorem approximation {d n D : ℕ} {f : Space d→ℝ} (hf : ContDiffOn ℝ (n+1) f (cube d))
    (hD : 1≤D) (spatialN K p a N cap : ℕ) (hK : 0<K) (hTags : tagCount d D<2^p)
    (hwidth : 2*N<2^a) (delta mu M H alpha tau : ℝ)
    (hdelta : 0<delta) (hmu : 0<mu) (hcap : mu*(cap:ℝ)=1) (hM : 0≤M) (hH : 0≤H)
    (ha : 0≤alpha) (htau : 0<tau) (scale : mu^(((n+1:ℕ):ℝ)+alpha)≤2*tau)
    (hN : 2*H*(D:ℝ)^(((n+1:ℕ):ℝ)+alpha)+commonBudget (n+1) D/2+1/2≤(N:ℝ))
    (holder : ∀y∈cube d,∀z∈cube d,
      ‖iteratedFDerivWithin ℝ (n+1) f (cube d) z-iteratedFDerivWithin ℝ (n+1) f (cube d) y‖≤H*‖z-y‖^alpha)
    (bound : ∀y∈cube d,∀r,r≤n+1 → ‖iteratedFDerivWithin ℝ r f (cube d) y‖≤M)
    (shift : Fin d→ℤ) (coarse fine : Fin d→ℕ) (hc : ∀j,coarse j≤spatialN) (hFine : ∀j,fine j<K)
    (x : Space d) (hx : x∈cube d)
    (safe : ∀j,MathCan.SpatialScalar.safeCell delta
      ((mu*(D:ℝ))⁻¹*x j+1-(shift j:ℝ)/(D:ℝ)) (coarse j*K+fine j)) :
    |f x-MathCan.WordTransport.evaluate
      (decoded (k:=n+1) (D:=D) spatialN K p a N cap hK delta mu M tau f shift coarse fine x)
      (mu⁻¹ • (x-point cap D mu shift coarse K fine))|≤
      H*(mu*(D:ℝ))^(((n+1:ℕ):ℝ)+alpha)/(Nat.factorial (n+1):ℝ)+
        (MathCan.WordTransport.size d (n+1):ℝ)*(D:ℝ)^(n+1)*(tau/2) := by
  let tags:=schedule cap D K hK mu shift coarse
  let a0:=point cap D mu shift coarse K (unrank K d 0)
  let sites:=querySites (mu*(D:ℝ)) (fun j=>(shift j:ℝ)/(D:ℝ)) coarse fine x
  have align : tags.length+1=K^sites.length := by
    simpa only [tags,sites,querySites,List.length_ofFn] using schedule_length cap D K hK mu shift coarse
  have inside : ∀i,i≤tags.length → anchors mu tags a0 i∈cube d :=
    schedule_inside cap D K hK mu hmu.le hcap.le shift coarse
  have selected : anchors mu tags a0 (snakeRank K (sites.map Site.fine))=
      point cap D mu shift coarse K fine := by
    rw [query_fine]
    exact schedule_selected cap D K hK mu shift coarse fine hFine
  have hdist : ‖x-anchors mu tags a0 (snakeRank K (sites.map Site.fine))‖≤mu*(D:ℝ) := by
    rw [selected,point_anchor cap D K (by omega) mu hmu hcap shift coarse fine]
    exact safe_coverage (mu*(D:ℝ)) delta (mul_pos hmu (by exact_mod_cast (show 0<D by omega)))
      hdelta x _ coarse fine K hx safe
  have hr:=CubeCapture.decoded_approximation hf hD spatialN K p a N hK hTags hwidth
    delta mu M H alpha tau (mu*(D:ℝ)) hdelta hmu (micro_scale_le_one cap mu hmu hcap) hM hH ha htau
    scale hN holder sites (query_valid spatialN K _ delta _ coarse fine x hc hFine safe)
    tags align a0 x inside hx bound hdist le_rfl
  rw [selected] at hr
  exact hr

end MathCan.CubeSpatial
