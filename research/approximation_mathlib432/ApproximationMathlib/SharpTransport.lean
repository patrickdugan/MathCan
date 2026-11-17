import ApproximationMathlib.MultivariateCapture

/-! Mesh-scaled multivariate Taylor transport.  A component of order r is
scaled by mu^r/r!, and its remaining Taylor order is m+1.  Thus the residual
has the total exponent r+m+1+alpha, including zero displacement. -/
namespace MathCan.SharpResidual
open MathCan.MultivariateTaylor MathCan.MultivariateHolder MathCan.MultivariateBounds
open Set
set_option autoImplicit false

noncomputable def scaledValue {d : ℕ} (mu : ℝ) (r : ℕ) (g : Space d → ℝ) (a : Space d) : ℝ :=
  mu^r/(Nat.factorial r:ℝ)*g a

noncomputable def scaledTaylor {d : ℕ} (mu : ℝ) (r m : ℕ)
    (g : Space d → ℝ) (a h : Space d) : ℝ :=
  mu^r/(Nat.factorial r:ℝ)*tensorPolynomial g m a h

noncomputable def component {d r : ℕ} (f : Space d → ℝ) (w : Fin r → Fin d) : Space d → ℝ :=
  fun x=>iteratedFDeriv ℝ r f x (fun j=>basis (w j))

theorem component_contDiff {d r m : ℕ} {f : Space d → ℝ}
    (hf : ContDiff ℝ (m+r) f) (w : Fin r → Fin d) :
    ContDiff ℝ m (component f w) := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r=>Space d) ℝ
    (fun j=>basis (w j))).contDiff.comp (hf.iteratedFDeriv_right (by norm_cast))

theorem scaled_tensor_residual {d m r : ℕ} {g : Space d → ℝ}
    (hg : ContDiff ℝ (m+1) g) (a h : Space d) (mu D H alpha : ℝ)
    (hmu : 0≤mu) (hD : 0≤D) (hH : 0≤H) (ha : 0≤alpha) (hh : ‖h‖≤mu*D)
    (holder : ∀t∈uIcc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ (m+1) g (a+t • h)-iteratedFDeriv ℝ (m+1) g a‖≤H*‖a+t • h-a‖^alpha) :
    |scaledValue mu r g (a+h)-scaledTaylor mu r (m+1) g a h|≤
      H*D^(((m+1:ℕ):ℝ)+alpha)*mu^((r:ℝ)+((m+1:ℕ):ℝ)+alpha)/
        ((Nat.factorial r:ℝ)*(Nat.factorial (m+1):ℝ)) := by
  have hr:=holder_tensor_remainder hg a h H alpha hH ha holder
  have hs : 0≤((m+1:ℕ):ℝ)+alpha := by positivity
  have hp:=Real.rpow_le_rpow (norm_nonneg h) hh hs
  have hn : 0≤mu^r/(Nat.factorial r:ℝ) := by positivity
  unfold scaledValue scaledTaylor
  rw [← mul_sub,abs_mul,abs_of_nonneg hn]
  calc
    _ ≤ (mu^r/(Nat.factorial r:ℝ))*(H*‖h‖^(((m+1:ℕ):ℝ)+alpha)/(Nat.factorial (m+1):ℝ)) :=
      mul_le_mul_of_nonneg_left hr hn
    _ ≤ (mu^r/(Nat.factorial r:ℝ))*(H*(mu*D)^(((m+1:ℕ):ℝ)+alpha)/(Nat.factorial (m+1):ℝ)) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hmu hD,
        show (r:ℝ)+((m+1:ℕ):ℝ)+alpha=(r:ℝ)+(((m+1:ℕ):ℝ)+alpha) by ring,
        Real.rpow_add_of_nonneg hmu (Nat.cast_nonneg r) hs,Real.rpow_natCast]
      ring

theorem normalized_tensor_residual {d m r : ℕ} {g : Space d → ℝ}
    (hg : ContDiff ℝ (m+1) g) (a h : Space d) (mu D H alpha tau : ℝ)
    (hmu : 0≤mu) (hD : 0≤D) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau)
    (hh : ‖h‖≤mu*D) (hscale : mu^((r:ℝ)+((m+1:ℕ):ℝ)+alpha)≤2*tau)
    (holder : ∀t∈uIcc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ (m+1) g (a+t • h)-iteratedFDeriv ℝ (m+1) g a‖≤H*‖a+t • h-a‖^alpha) :
    |scaledValue mu r g (a+h)-scaledTaylor mu r (m+1) g a h|/tau≤
      2*H*D^(((m+1:ℕ):ℝ)+alpha)/((Nat.factorial r:ℝ)*(Nat.factorial (m+1):ℝ)) := by
  have hr:=scaled_tensor_residual (r:=r) hg a h mu D H alpha hmu hD hH ha hh holder
  have hb:=mul_le_mul_of_nonneg_left hscale
    (show 0≤H*D^(((m+1:ℕ):ℝ)+alpha) by positivity)
  have hf : (0:ℝ)<(Nat.factorial r:ℝ)*(Nat.factorial (m+1):ℝ) := by positivity
  calc
    _ ≤ (H*D^(((m+1:ℕ):ℝ)+alpha)*mu^((r:ℝ)+((m+1:ℕ):ℝ)+alpha)/
      ((Nat.factorial r:ℝ)*(Nat.factorial (m+1):ℝ)))/tau := div_le_div_of_nonneg_right hr htau.le
    _ ≤ (H*D^(((m+1:ℕ):ℝ)+alpha)*(2*tau)/
      ((Nat.factorial r:ℝ)*(Nat.factorial (m+1):ℝ)))/tau := by gcongr
    _ = _ := by field_simp

/-- The top derivative component has a degree-zero transport polynomial. -/
theorem top_component_residual {d r : ℕ} {f : Space d → ℝ}
    (a h : Space d) (w : Fin r → Fin d) (mu D H alpha tau : ℝ)
    (hmu : 0≤mu) (hD : 0≤D) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau)
    (hh : ‖h‖≤mu*D) (hscale : mu^((r:ℝ)+alpha)≤2*tau)
    (holder : ‖iteratedFDeriv ℝ r f (a+h)-iteratedFDeriv ℝ r f a‖≤H*‖h‖^alpha) :
    |mu^r/(Nat.factorial r:ℝ)*
      (iteratedFDeriv ℝ r f (a+h) (fun j=>basis (w j))-
       iteratedFDeriv ℝ r f a (fun j=>basis (w j)))|/tau≤
      2*H*D^alpha/(Nat.factorial r:ℝ) := by
  have hc:=component_bound (iteratedFDeriv ℝ r f (a+h)-iteratedFDeriv ℝ r f a) w
  simp only [ContinuousMultilinearMap.sub_apply] at hc
  have hp:=Real.rpow_le_rpow (norm_nonneg h) hh ha
  have hb:=mul_le_mul_of_nonneg_left hscale (show 0≤H*D^alpha by positivity)
  have hn : 0≤mu^r/(Nat.factorial r:ℝ) := by positivity
  rw [abs_mul,abs_of_nonneg hn]
  calc
    _ ≤ (mu^r/(Nat.factorial r:ℝ))*(H*‖h‖^alpha)/tau := by
      apply div_le_div_of_nonneg_right _ htau.le
      exact mul_le_mul_of_nonneg_left (hc.trans holder) hn
    _ ≤ (mu^r/(Nat.factorial r:ℝ))*(H*(mu*D)^alpha)/tau := by gcongr
    _ = (H*D^alpha*mu^((r:ℝ)+alpha)/(Nat.factorial r:ℝ))/tau := by
      rw [Real.mul_rpow hmu hD,Real.rpow_add_of_nonneg hmu (Nat.cast_nonneg r) ha,Real.rpow_natCast]
      ring
    _ ≤ (H*D^alpha*(2*tau)/(Nat.factorial r:ℝ))/tau := by gcongr
    _ = _ := by field_simp

end MathCan.SharpResidual


/-! Genuine derivative components: the highest-derivative Holder hypothesis
propagates to every component field, without a mixed-partial symmetry oracle. -/
namespace MathCan.SharpJet
open MathCan.MultivariateTaylor MathCan.SharpResidual
set_option autoImplicit false

theorem isometry_derivative_difference
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : F ≃ₗᵢ[ℝ] G) (g : E → F) (m : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ m (e ∘ g) x-iteratedFDeriv ℝ m (e ∘ g) y‖=
      ‖iteratedFDeriv ℝ m g x-iteratedFDeriv ℝ m g y‖ := by
  have he : iteratedFDeriv ℝ m (e ∘ g) x-iteratedFDeriv ℝ m (e ∘ g) y=
      e.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ m g x-iteratedFDeriv ℝ m g y) := by
    change iteratedFDeriv ℝ m (e.toContinuousLinearEquiv ∘ g) x-
      iteratedFDeriv ℝ m (e.toContinuousLinearEquiv ∘ g) y=_
    rw [e.toContinuousLinearEquiv.iteratedFDeriv_comp_left,
      e.toContinuousLinearEquiv.iteratedFDeriv_comp_left]
    ext v
    simp
  rw [he]
  exact e.toLinearIsometry.norm_compContinuousMultilinearMap _

theorem fderiv_derivative_difference
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (m : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ m (fderiv ℝ g) x-iteratedFDeriv ℝ m (fderiv ℝ g) y‖=
      ‖iteratedFDeriv ℝ (m+1) g x-iteratedFDeriv ℝ (m+1) g y‖ := by
  simp only [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply]
  simpa only [dist_eq_norm] using ((continuousMultilinearCurryRightEquiv' ℝ m E F).symm.isometry.dist_eq
    (iteratedFDeriv ℝ m (fderiv ℝ g) x) (iteratedFDeriv ℝ m (fderiv ℝ g) y)).symm

theorem iterated_derivative_difference
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (r m : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) x-
      iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) y‖=
      ‖iteratedFDeriv ℝ (m+r) f x-iteratedFDeriv ℝ (m+r) f y‖ := by
  induction r generalizing m with
  | zero =>
    simpa only [Nat.add_zero,iteratedFDeriv_zero_eq_comp] using
      isometry_derivative_difference (continuousMultilinearCurryFin0 ℝ E F).symm f m x y
  | succ r ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    calc
      _ = ‖iteratedFDeriv ℝ m (fderiv ℝ (iteratedFDeriv ℝ r f)) x-
          iteratedFDeriv ℝ m (fderiv ℝ (iteratedFDeriv ℝ r f)) y‖ :=
        isometry_derivative_difference
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1)=>E) F).symm
          (fderiv ℝ (iteratedFDeriv ℝ r f)) m x y
      _ = ‖iteratedFDeriv ℝ (m+1) (iteratedFDeriv ℝ r f) x-
          iteratedFDeriv ℝ (m+1) (iteratedFDeriv ℝ r f) y‖ :=
        fderiv_derivative_difference (iteratedFDeriv ℝ r f) m x y
      _ = _ := (ih (m+1)).trans (congrArg
        (fun n=>‖iteratedFDeriv ℝ n f x-iteratedFDeriv ℝ n f y‖)
        (show (m+1)+r=m+(r+1) by omega))

theorem component_derivative_difference {d r m : ℕ} {f : Space d → ℝ}
    (hf : ContDiff ℝ (m+r) f) (w : Fin r → Fin d) (x y : Space d) :
    ‖iteratedFDeriv ℝ m (component f w) x-iteratedFDeriv ℝ m (component f w) y‖≤
      ‖iteratedFDeriv ℝ (m+r) f x-iteratedFDeriv ℝ (m+r) f y‖ := by
  let e:=ContinuousMultilinearMap.apply ℝ (fun _ : Fin r=>Space d) ℝ (fun j=>basis (w j))
  have hd : ContDiff ℝ m (iteratedFDeriv ℝ r f) := hf.iteratedFDeriv_right (by norm_cast)
  have he : iteratedFDeriv ℝ m (component f w) x-iteratedFDeriv ℝ m (component f w) y=
      e.compContinuousMultilinearMap (iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) x-
        iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) y) := by
    change iteratedFDeriv ℝ m (e ∘ iteratedFDeriv ℝ r f) x-
      iteratedFDeriv ℝ m (e ∘ iteratedFDeriv ℝ r f) y=_
    rw [e.iteratedFDeriv_comp_left hd.contDiffAt le_rfl,e.iteratedFDeriv_comp_left hd.contDiffAt le_rfl]
    ext v
    simp
  rw [he,← iterated_derivative_difference f r m x y]
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  change ‖(iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) x v-
    iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) y v) (fun j=>basis (w j))‖≤_
  have hb:=MathCan.MultivariateBounds.component_bound
    (iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) x v-
      iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) y v) w
  exact hb.trans ((iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) x-
    iteratedFDeriv ℝ m (iteratedFDeriv ℝ r f) y).le_opNorm v)

theorem sharp_component_transport {d r m : ℕ} {f : Space d → ℝ}
    (hf : ContDiff ℝ ((m+1)+r) f) (a h : Space d) (w : Fin r → Fin d)
    (mu D H alpha tau : ℝ) (hmu : 0≤mu) (hD : 0≤D) (hH : 0≤H) (ha : 0≤alpha)
    (htau : 0<tau) (hh : ‖h‖≤mu*D) (scale : mu^((r:ℝ)+((m+1:ℕ):ℝ)+alpha)≤2*tau)
    (holder : ∀t,t∈Set.uIcc (0:ℝ) 1 →
      ‖iteratedFDeriv ℝ ((m+1)+r) f (a+t • h)-iteratedFDeriv ℝ ((m+1)+r) f a‖≤H*‖a+t • h-a‖^alpha) :
    |scaledValue mu r (component f w) (a+h)-scaledTaylor mu r (m+1) (component f w) a h|/tau≤
      2*H*D^(((m+1:ℕ):ℝ)+alpha)/((Nat.factorial r:ℝ)*(Nat.factorial (m+1):ℝ)) := by
  apply normalized_tensor_residual (component_contDiff hf w) a h mu D H alpha tau
    hmu hD hH ha htau hh scale
  intro t ht
  exact (component_derivative_difference hf w (a+t • h) a).trans (holder t ht)

theorem uniform_component_budget (r m k : ℕ) (D H alpha : ℝ)
    (hD : 1≤D) (hH : 0≤H) (hm : m≤k) :
    2*H*D^((m:ℝ)+alpha)/((Nat.factorial r:ℝ)*(Nat.factorial m:ℝ))≤
      2*H*D^((k:ℝ)+alpha) := by
  have hD0 : 0≤D := by linarith
  have hmk : (m:ℝ)≤(k:ℝ) := by exact_mod_cast hm
  have hexp : (m:ℝ)+alpha≤(k:ℝ)+alpha := by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hD hexp
  have hfac : (1:ℝ)≤(Nat.factorial r:ℝ)*(Nat.factorial m:ℝ) := by
    exact_mod_cast (show 1≤Nat.factorial r*Nat.factorial m by
      exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.factorial_pos r) (Nat.factorial_pos m)))
  exact (div_le_self (by positivity) hfac).trans (mul_le_mul_of_nonneg_left hp (by positivity))

/-- All derivative ranks share one normalized residual budget, including the
top rank (degree-zero transport). The Holder hypothesis is on the original
highest Frechet derivative, not on an abstract residual. -/
theorem sharp_jet_transport {d r m k : ℕ} {f : Space d → ℝ}
    (hf : ContDiff ℝ k f) (order : m+r=k) (a h : Space d) (w : Fin r → Fin d)
    (mu D H alpha tau : ℝ) (hmu : 0≤mu) (hD : 1≤D) (hH : 0≤H) (ha : 0≤alpha)
    (htau : 0<tau) (hh : ‖h‖≤mu*D) (scale : mu^((k:ℝ)+alpha)≤2*tau)
    (holder : ∀t,t∈Set.uIcc (0:ℝ) 1 →
      ‖iteratedFDeriv ℝ k f (a+t • h)-iteratedFDeriv ℝ k f a‖≤H*‖a+t • h-a‖^alpha) :
    |scaledValue mu r (component f w) (a+h)-scaledTaylor mu r m (component f w) a h|/tau≤
      2*H*D^((k:ℝ)+alpha) := by
  cases m with
  | zero =>
    have hr : r=k := by omega
    have htop : ‖iteratedFDeriv ℝ r f (a+h)-iteratedFDeriv ℝ r f a‖≤H*‖h‖^alpha := by
      rw [hr]
      simpa using holder 1 (by simp)
    have hs : mu^((r:ℝ)+alpha)≤2*tau := by simpa [hr] using scale
    have hb:=top_component_residual a h w mu D H alpha tau hmu (by linarith) hH ha htau hh hs htop
    have he : scaledValue mu r (component f w) (a+h)-scaledTaylor mu r 0 (component f w) a h=
        mu^r/(Nat.factorial r:ℝ)*(component f w (a+h)-component f w a) := by
      simp [scaledValue,scaledTaylor,tensorPolynomial,mul_sub]
    rw [he]
    exact hb.trans (by simpa using uniform_component_budget r 0 k D H alpha hD hH (by omega))
  | succ m =>
    have hord : (m+1)+r=k := by omega
    have hsmooth : ContDiff ℝ ((m+1)+r) f :=
      hf.of_le (by exact_mod_cast (show (m+1)+r≤k by omega))
    have hs : mu^((r:ℝ)+((m+1:ℕ):ℝ)+alpha)≤2*tau := by
      have he : (r:ℝ)+((m:ℝ)+1)=(k:ℝ) := by exact_mod_cast (show r+(m+1)=k by omega)
      simpa only [Nat.cast_add,Nat.cast_one,he] using scale
    have hb:=sharp_component_transport hsmooth a h w mu D H alpha tau hmu (by linarith) hH ha htau hh hs
      (by rw [hord]; exact holder)
    exact hb.trans (uniform_component_budget r (m+1) k D H alpha hD hH (by omega))

end MathCan.SharpJet


/-! Bounded correction alphabets from the true-jet transport residual.
The residual contract is explicit; it is distinct from coefficient accuracy,
which is proved for the rounded, clipped, decoded trajectory. -/
namespace MathCan.SharpAlphabet
open MathCan.JetSynthesis MathCan.FrameSynthesis MathCan.TaylorFrame
open MathCan.TaylorTransport MathCan.CommonGateBound MathCan.ConcreteJetCapture
open MathCan.SpatialScalar MathCan.SpatialNormalized MathCan.SpatialRouting
open MathCan.CommonGateCapture MathCan.CapturedApproximation
set_option autoImplicit false

theorem prediction_error {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (tau : ℝ) (htau : 0<tau)
    (s : Step d) (hs : s.magnitude≤D) (v u : Fin J → ℝ)
    (accurate : ∀j,|v j-u j|≤tau/2) (beta : Fin J) :
    |prediction indices s v beta-prediction indices s u beta|≤
      (tau/2)*commonBudget k D := by
  have h:=prediction_bound indices k D hD injective degree (tau/2) (by positivity)
    s hs (fun j=>v j-u j) (fun j=>abs_le.mp (accurate j)) beta
  simpa only [prediction,transport_sub] using h

theorem innovation_bound {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (tau B : ℝ) (htau : 0<tau)
    (s : Step d) (hs : s.magnitude≤D) (target u v : Fin J → ℝ)
    (residual : ∀j,|target j-prediction indices s u j|≤B*tau)
    (accurate : ∀j,|v j-u j|≤tau/2) (beta : Fin J) :
    |(target beta-prediction indices s v beta)/tau|≤B+commonBudget k D/2 := by
  have hp:=prediction_error indices k D hD injective degree tau htau s hs v u accurate beta
  have hr:=residual beta
  have ht:=abs_sub_le (target beta) (prediction indices s u beta) (prediction indices s v beta)
  rw [abs_sub_comm (prediction indices s u beta)] at ht
  rw [abs_div,abs_of_pos htau,div_le_iff₀ htau]
  nlinarith

theorem sharp_frame {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D N a : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (C tau B : ℝ) (htau : 0<tau)
    (hN : B+commonBudget k D/2+1/2≤(N:ℝ)) (hwidth : 2*N<2^a)
    (s : Step d) (hs : s.magnitude≤D) (target u v : Fin J → ℝ)
    (residual : ∀j,|target j-prediction indices s u j|≤B*tau)
    (accurate : ∀j,|v j-u j|≤tau/2) :
    validFrame D a (frame indices N tau s target v) ∧
    directUpdate indices C (N:ℝ) tau (frame indices N tau s target v) v=update indices C tau s target v := by
  have hc:∀beta,-(N:ℤ)≤correction tau (target beta) (prediction indices s v beta) ∧
      correction tau (target beta) (prediction indices s v beta)≤(N:ℤ) := by
    intro beta
    exact correction_bound tau _ _ _ N
      (innovation_bound indices k D hD injective degree tau B htau s hs target u v residual accurate beta) hN
  exact ⟨⟨hs,fun beta=>code_bound N a _ (hc beta) hwidth⟩,
    frame_update indices N C tau s target v (fun beta=>(hc beta).1)⟩

/-- Analytic Taylor estimates discharge the residual contract.  The equations
state exactly the algebraic identification required of a concrete jet layout. -/
theorem analytic_sharp_frame {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D N a : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (C tau B mu H alpha : ℝ)
    (htau : 0<tau) (hmu : 0≤mu) (hH : 0≤H) (ha : 0≤alpha)
    (hN : B+commonBudget k D/2+1/2≤(N:ℝ)) (hwidth : 2*N<2^a)
    (s : Step d) (hs : s.magnitude≤D) (target u v : Fin J → ℝ)
    (r m : Fin J → ℕ) (g : Fin J → MathCan.MultivariateTaylor.Space d → ℝ)
    (anchor h : MathCan.MultivariateTaylor.Space d) (hh : ‖h‖≤mu*(D:ℝ))
    (smooth : ∀j,ContDiff ℝ (m j+1) (g j))
    (holder : ∀j t,t∈Set.uIcc (0:ℝ) 1 →
      ‖iteratedFDeriv ℝ (m j+1) (g j) (anchor+t • h)-iteratedFDeriv ℝ (m j+1) (g j) anchor‖≤
        H*‖anchor+t • h-anchor‖^alpha)
    (scale : ∀j,mu^((r j:ℝ)+((m j+1:ℕ):ℝ)+alpha)≤2*tau)
    (budget : ∀j,2*H*(D:ℝ)^(((m j+1:ℕ):ℝ)+alpha)/
      ((Nat.factorial (r j):ℝ)*(Nat.factorial (m j+1):ℝ))≤B)
    (target_eq : ∀j,target j=MathCan.SharpResidual.scaledValue mu (r j) (g j) (anchor+h))
    (transport_eq : ∀j,prediction indices s u j=
      MathCan.SharpResidual.scaledTaylor mu (r j) (m j+1) (g j) anchor h)
    (accurate : ∀j,|v j-u j|≤tau/2) :
    validFrame D a (frame indices N tau s target v) ∧
    directUpdate indices C (N:ℝ) tau (frame indices N tau s target v) v=update indices C tau s target v := by
  apply sharp_frame indices k D N a hD injective degree C tau B htau hN hwidth s hs target u v _ accurate
  intro j
  have hr:=MathCan.SharpResidual.normalized_tensor_residual (smooth j) anchor h mu (D:ℝ) H alpha tau
    hmu (Nat.cast_nonneg D) hH ha htau hh (scale j) (holder j)
  rw [← target_eq j,← transport_eq j,div_le_iff₀ htau] at hr
  exact hr.trans (mul_le_mul_of_nonneg_right (budget j) htau.le)

theorem component_sharp_frame {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D N a : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) {f : MathCan.MultivariateTaylor.Space d → ℝ}
    (hf : ContDiff ℝ k f) (C tau mu H alpha : ℝ)
    (htau : 0<tau) (hmu : 0≤mu) (hH : 0≤H) (ha : 0≤alpha)
    (hN : 2*H*(D:ℝ)^((k:ℝ)+alpha)+commonBudget k D/2+1/2≤(N:ℝ)) (hwidth : 2*N<2^a)
    (s : Step d) (hs : s.magnitude≤D) (target u v : Fin J → ℝ)
    (r m : Fin J → ℕ) (order : ∀j,m j+r j=k) (w : ∀j,Fin (r j) → Fin d)
    (anchor h : MathCan.MultivariateTaylor.Space d) (hh : ‖h‖≤mu*(D:ℝ))
    (holder : ∀t,t∈Set.uIcc (0:ℝ) 1 →
      ‖iteratedFDeriv ℝ k f (anchor+t • h)-iteratedFDeriv ℝ k f anchor‖≤H*‖anchor+t • h-anchor‖^alpha)
    (scale : mu^((k:ℝ)+alpha)≤2*tau)
    (target_eq : ∀j,target j=MathCan.SharpResidual.scaledValue mu (r j)
      (MathCan.SharpResidual.component f (w j)) (anchor+h))
    (transport_eq : ∀j,prediction indices s u j=MathCan.SharpResidual.scaledTaylor mu (r j) (m j)
      (MathCan.SharpResidual.component f (w j)) anchor h)
    (accurate : ∀j,|v j-u j|≤tau/2) :
    validFrame D a (frame indices N tau s target v) ∧
    directUpdate indices C (N:ℝ) tau (frame indices N tau s target v) v=update indices C tau s target v := by
  apply sharp_frame indices k D N a hD injective degree C tau (2*H*(D:ℝ)^((k:ℝ)+alpha))
    htau hN hwidth s hs target u v _ accurate
  intro j
  have hd : (1:ℝ)≤(D:ℝ) := by exact_mod_cast hD
  have hb:=MathCan.SharpJet.sharp_jet_transport hf (order j) anchor h (w j) mu (D:ℝ) H alpha tau
    hmu hd hH ha htau hh scale holder
  rw [← target_eq j,← transport_eq j,div_le_iff₀ htau] at hb
  exact hb

def Residuals {d J : ℕ} (indices : Fin J → Fin d → ℕ) (tau B : ℝ) :
    List (Step d) → (ℕ → Fin J → ℝ) → Prop
  | [],_ => True
  | s::tail,u => (∀beta,|u 1 beta-prediction indices s (u 0) beta|≤B*tau) ∧
      Residuals indices tau B tail (fun i=>u (i+1))

theorem sharp_frames {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D N a : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (C tau B : ℝ) (hC : 0≤C) (htau : 0<tau)
    (hN : B+commonBudget k D/2+1/2≤(N:ℝ)) (hwidth : 2*N<2^a)
    (steps : List (Step d)) (valid : ∀s,s∈steps → s.magnitude≤D)
    (targets : ℕ → Fin J → ℝ) (residuals : Residuals indices tau B steps targets)
    (bounded : ∀i,i≤steps.length → ∀beta,-C≤targets i beta ∧ targets i beta≤C)
    (v : Fin J → ℝ) (accurate : ∀beta,|v beta-targets 0 beta|≤tau/2) :
    (∀f,f∈frames indices N C tau steps targets v → validFrame D a f) ∧
    (∀i,referenceAt indices C (N:ℝ) tau (frames indices N C tau steps targets v) v i=
      states indices C tau steps targets v i) := by
  induction steps generalizing targets v with
  | nil => exact ⟨by simp [frames],by intro i; cases i <;> rfl⟩
  | cons s tail ih =>
    have head:=sharp_frame indices k D N a hD injective degree C tau B htau hN hwidth
      s (valid s (by simp)) (targets 1) (targets 0) v residuals.1 accurate
    have rest:=ih (fun t ht=>valid t (by simp [ht])) (fun i=>targets (i+1)) residuals.2
      (fun i hi=>bounded (i+1) (by simp only [List.length_cons]; omega))
      (update indices C tau s (targets 1) v)
      (update_accuracy indices C tau hC htau s _ v (bounded 1 (by simp)))
    constructor
    · intro f hf
      simp only [frames,List.mem_cons] at hf
      rcases hf with he | he
      · subst f; exact head.1
      · exact rest.1 f he
    · intro i
      cases i with
      | zero => rfl
      | succ i => simp only [frames,referenceAt,states]; rw [head.2]; exact rest.2 i

theorem sharp_decoded_accuracy (spatialN K d J k D N p a : ℕ) (hK : 0<K)
    (delta : ℝ) (hdelta : 0<delta) (sites : List (Site ℝ)) (dimension : sites.length=d)
    (safe : validSites spatialN K delta sites) (indices : Fin J → Fin d → ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (hamp : D<2^p)
    (C tau B : ℝ) (hC : 0≤C) (htau : 0<tau)
    (hN : B+commonBudget k D/2+1/2≤(N:ℝ)) (hwidth : 2*N<2^a)
    (steps : List (Step d)) (valid : ∀s,s∈steps → s.magnitude≤D)
    (alignment : steps.length+1=K^d) (targets : ℕ → Fin J → ℝ)
    (residuals : Residuals indices tau B steps targets)
    (bounded : ∀i,i≤steps.length → ∀beta,-C≤targets i beta ∧ targets i beta≤C) :
    ∀beta,|capturedCoefficients spatialN K k D p a delta sites indices C (N:ℝ) tau
      (frames indices N C tau steps targets (initial C tau (targets 0)))
      (initial C tau (targets 0)) beta-targets (snakeRank K (sites.map Site.fine)) beta|≤tau/2 := by
  let v:=initial C tau (targets 0)
  have hi:=initial_accuracy C tau hC htau (targets 0) (bounded 0 (by omega))
  have hs:=sharp_frames indices k D N a hD injective degree C tau B hC htau hN hwidth
    steps valid targets residuals bounded v hi
  have hc:=common_spatial_capture spatialN K d J hK delta hdelta sites dimension safe indices
    k D p a hD injective degree hamp C (N:ℝ) tau hC (frames indices N C tau steps targets v)
    hs.1 (by rw [frames_length]; exact alignment) v (initial_range C tau hC _)
  have he : capturedCoefficients spatialN K k D p a delta sites indices C (N:ℝ) tau
      (frames indices N C tau steps targets v) v=
      referenceAt indices C (N:ℝ) tau (frames indices N C tau steps targets v) v
        (snakeRank K (sites.map Site.fine)) := hc.2
  rw [he,hs.2]
  exact states_accuracy indices C tau hC htau steps targets bounded v hi _
    (by simpa only [frames_length] using hc.1)

end MathCan.SharpAlphabet


/-! The approximation theorem with a mesh-independent correction alphabet.
The true-jet residual is an explicit analytic contract, not a coefficient-
accuracy assumption. SharpResidual supplies analytic scaled Taylor estimates;
identifying that Taylor polynomial with the concrete matrix is a separate
algebraic obligation for a chosen normalized jet layout. -/
namespace MathCan.SharpCapture
open MathCan.MultivariateTaylor MathCan.MultivariateBounds MathCan.MultivariateHolder
open MathCan.JetSynthesis MathCan.FrameSynthesis MathCan.SynthesisCapture
open MathCan.CommonGateBound MathCan.SharpAlphabet
open MathCan.CapturedApproximation (capturedCoefficients)
open MathCan.SpatialNormalized MathCan.SpatialScalar MathCan.SpatialRouting
set_option autoImplicit false

noncomputable def targets {d : ℕ} (f : Space d→ℝ) (k : ℕ) (anchors : ℕ→Space d) :
    ℕ→Fin (size d k)→ℝ := fun i=>coefficients f k (anchors i)

noncomputable def capturedJet {d : ℕ} (f : Space d→ℝ) (k : ℕ) (anchors : ℕ→Space d)
    (spatialN K D N p a : ℕ) (delta C tau : ℝ) (sites : List (Site ℝ)) (steps : List (Step d)) :
    Fin (size d k)→ℝ :=
  let u:=targets f k anchors
  let v:=initial C tau (u 0)
  capturedCoefficients spatialN K k D p a delta sites (labels d k) C (N:ℝ) tau
    (frames (labels d k) N C tau steps u v) v

theorem jet_accuracy {d k : ℕ} (f : Space d→ℝ) (anchors : ℕ→Space d)
    (spatialN K D N p a : ℕ) (hK : 0<K) (hD : 1≤D) (delta : ℝ) (hdelta : 0<delta)
    (sites : List (Site ℝ)) (dimension : sites.length=d) (safe : validSites spatialN K delta sites)
    (steps : List (Step d)) (valid : ∀s,s∈steps → s.magnitude≤D) (alignment : steps.length+1=K^d)
    (M tau B : ℝ) (hM : 0≤M) (htau : 0<tau)
    (jetBound : ∀i,i≤steps.length → ∀n,n≤k → ‖iteratedFDeriv ℝ n f (anchors i)‖≤M)
    (residuals : Residuals (labels d k) tau B steps (targets f k anchors))
    (hamp : D<2^p) (hN : B+commonBudget k D/2+1/2≤(N:ℝ))
    (hwidth : 2*N<2^a) :
    ∀beta,|capturedJet f k anchors spatialN K D N p a delta (budget d k*M) tau sites steps beta-
      coefficients f k (anchors (snakeRank K (sites.map Site.fine))) beta|≤tau/2 := by
  have bounded:∀i,i≤steps.length → ∀beta,
      -(budget d k*M)≤targets f k anchors i beta ∧ targets f k anchors i beta≤budget d k*M := by
    intro i hi beta
    exact abs_le.mp (coefficients_bound (anchors i) M hM (jetBound i hi) beta)
  exact sharp_decoded_accuracy spatialN K d (size d k) k D N p a hK delta hdelta sites dimension safe
    (labels d k) hD (fun j l he=>labels_injective d k he) (labels_degree d k) hamp (budget d k*M) tau B
    (mul_nonneg (budget_nonneg d k) hM) htau hN hwidth steps valid alignment (targets f k anchors) residuals bounded

theorem smooth_decoded_approximation {d n : ℕ} {f : Space d→ℝ} (hf : ContDiff ℝ (n+1) f)
    (anchors : ℕ→Space d) (spatialN K D N p a : ℕ) (hK : 0<K) (hD : 1≤D)
    (delta : ℝ) (hdelta : 0<delta) (sites : List (Site ℝ)) (dimension : sites.length=d)
    (safe : validSites spatialN K delta sites) (steps : List (Step d))
    (valid : ∀s,s∈steps → s.magnitude≤D) (alignment : steps.length+1=K^d)
    (M tau rho B : ℝ) (hM : 0≤M) (htau : 0<tau) (hrho : rho≤1) (x : Space d)
    (jetBound : ∀i,i≤steps.length → ∀j,j≤n → ‖iteratedFDeriv ℝ j f (anchors i)‖≤M)
    (residuals : Residuals (labels d n) tau B steps (targets f n anchors))
    (hamp : D<2^p) (hN : B+commonBudget n D/2+1/2≤(N:ℝ))
    (hwidth : 2*N<2^a)
    (hdist : ‖x-anchors (snakeRank K (sites.map Site.fine))‖≤rho)
    (remainderBound : ∀t∈Set.uIcc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ (n+1) f (anchors (snakeRank K (sites.map Site.fine))+
        t • (x-anchors (snakeRank K (sites.map Site.fine))))‖≤M) :
    |f x-evaluate (capturedJet f n anchors spatialN K D N p a delta (budget d n*M) tau sites steps)
      (x-anchors (snakeRank K (sites.map Site.fine)))|≤
      M*rho^(n+1)/(Nat.factorial (n+1):ℝ)+(size d n:ℝ)*(tau/2) := by
  exact smooth_multivariate_approximation hf _ x M rho (tau/2) hM hdist hrho (by positivity)
    remainderBound _ (jet_accuracy f anchors spatialN K D N p a hK hD delta hdelta sites dimension safe
      steps valid alignment M tau B hM htau jetBound residuals hamp hN hwidth)

theorem holder_decoded_approximation {d n : ℕ} {f : Space d→ℝ} (hf : ContDiff ℝ (n+1) f)
    (anchors : ℕ→Space d) (spatialN K D N p a : ℕ) (hK : 0<K) (hD : 1≤D)
    (delta : ℝ) (hdelta : 0<delta) (sites : List (Site ℝ)) (dimension : sites.length=d)
    (safe : validSites spatialN K delta sites) (steps : List (Step d))
    (valid : ∀s,s∈steps → s.magnitude≤D) (alignment : steps.length+1=K^d)
    (M H alpha tau rho B : ℝ) (hM : 0≤M) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau) (hrho : rho≤1) (x : Space d)
    (jetBound : ∀i,i≤steps.length → ∀j,j≤n+1 → ‖iteratedFDeriv ℝ j f (anchors i)‖≤M)
    (residuals : Residuals (labels d (n+1)) tau B steps (targets f (n+1) anchors))
    (hamp : D<2^p)
    (hN : B+commonBudget (n+1) D/2+1/2≤(N:ℝ))
    (hwidth : 2*N<2^a) (hdist : ‖x-anchors (snakeRank K (sites.map Site.fine))‖≤rho)
    (holder : ∀t∈Set.uIcc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ (n+1) f (anchors (snakeRank K (sites.map Site.fine))+
        t • (x-anchors (snakeRank K (sites.map Site.fine))))-
        iteratedFDeriv ℝ (n+1) f (anchors (snakeRank K (sites.map Site.fine)))‖≤
      H*‖anchors (snakeRank K (sites.map Site.fine))+t • (x-anchors (snakeRank K (sites.map Site.fine)))-
        anchors (snakeRank K (sites.map Site.fine))‖^alpha) :
    |f x-evaluate (capturedJet f (n+1) anchors spatialN K D N p a delta (budget d (n+1)*M) tau sites steps)
      (x-anchors (snakeRank K (sites.map Site.fine)))|≤
      H*rho^(((n+1:ℕ):ℝ)+alpha)/(Nat.factorial (n+1):ℝ)+(size d (n+1):ℝ)*(tau/2) := by
  exact holder_multivariate_approximation hf _ x H alpha rho (tau/2) hH ha hdist hrho (by positivity)
    holder _ (jet_accuracy f anchors spatialN K D N p a hK hD delta hdelta sites dimension safe
      steps valid alignment M tau B hM htau jetBound residuals hamp hN hwidth)

end MathCan.SharpCapture


/-! A completely instantiated bounded-alphabet case in every dimension:
degree-zero jets of a globally Holder function. No residual, transport-identity,
or coefficient-accuracy premise remains in this specialization. -/
namespace MathCan.HolderCapture
open MathCan.MultivariateTaylor MathCan.SharpAlphabet MathCan.JetSynthesis
open MathCan.FrameSynthesis MathCan.TaylorTransport MathCan.TaylorPolynomial
open MathCan.CapturedApproximation MathCan.SpatialNormalized MathCan.SpatialScalar MathCan.SpatialRouting
set_option autoImplicit false

def constantIndex (d : ℕ) : Fin 1 → Fin d → ℕ := fun _ _=>0

theorem constant_prediction {d : ℕ} (s : Step d) (v : Fin 1 → ℝ) (beta : Fin 1) :
    prediction (constantIndex d) s v beta=v beta := by
  have hb : beta=0 := Fin.eq_zero beta
  subst beta
  simp [prediction,transport,constantIndex,entry,compatible,choose_zero,
    MathCan.TaylorPolynomial.total,List.ofFn_succ]

theorem holder_step_residual {d : ℕ} {f : Space d → ℝ}
    (a b : Space d) (mu D H alpha tau : ℝ) (hmu : 0≤mu) (hD : 0≤D)
    (hH : 0≤H) (ha : 0≤alpha) (_htau : 0<tau)
    (holder : |f b-f a|≤H*‖b-a‖^alpha) (hdist : ‖b-a‖≤mu*D)
    (scale : mu^alpha≤2*tau) : |f b-f a|≤(2*H*D^alpha)*tau := by
  have hp:=Real.rpow_le_rpow (norm_nonneg (b-a)) hdist ha
  have hb:=mul_le_mul_of_nonneg_left scale (show 0≤H*D^alpha by positivity)
  calc
    _ ≤ H*(mu*D)^alpha := holder.trans (mul_le_mul_of_nonneg_left hp hH)
    _ = H*D^alpha*mu^alpha := by rw [Real.mul_rpow hmu hD]; ring
    _ ≤ H*D^alpha*(2*tau) := hb
    _ = _ := by ring

theorem holder_residuals {d : ℕ} {f : Space d → ℝ} (steps : List (Step d))
    (anchors : ℕ → Space d) (mu D H alpha tau : ℝ) (hmu : 0≤mu) (hD : 0≤D)
    (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau)
    (holder : ∀a b,|f b-f a|≤H*‖b-a‖^alpha) (scale : mu^alpha≤2*tau)
    (distances : ∀i,i<steps.length → ‖anchors (i+1)-anchors i‖≤mu*D) :
    Residuals (constantIndex d) tau (2*H*D^alpha) steps (fun i _=>f (anchors i)) := by
  induction steps generalizing anchors with
  | nil => trivial
  | cons s tail ih =>
    constructor
    · intro beta
      rw [constant_prediction]
      exact holder_step_residual (anchors 0) (anchors 1) mu D H alpha tau hmu hD hH ha htau
        (holder _ _) (distances 0 (by simp)) scale
    · apply ih (fun i=>anchors (i+1))
      intro i hi
      exact distances (i+1) (by simp only [List.length_cons]; omega)

noncomputable def capturedValue {d : ℕ} (f : Space d → ℝ) (anchors : ℕ → Space d)
    (spatialN K D N p a : ℕ) (delta C tau : ℝ) (sites : List (Site ℝ)) (steps : List (Step d)) : ℝ :=
  let u : ℕ → Fin 1 → ℝ:=fun i _=>f (anchors i)
  let v:=initial C tau (u 0)
  capturedCoefficients spatialN K 0 D p a delta sites (constantIndex d) C (N:ℝ) tau
    (frames (constantIndex d) N C tau steps u v) v 0

theorem holder_decoded_approximation {d : ℕ} {f : Space d → ℝ}
    (anchors : ℕ → Space d) (spatialN K D N p a : ℕ) (hK : 0<K) (hD : 1≤D)
    (delta : ℝ) (hdelta : 0<delta) (sites : List (Site ℝ)) (dimension : sites.length=d)
    (safe : validSites spatialN K delta sites) (steps : List (Step d))
    (valid : ∀s,s∈steps → s.magnitude≤D) (alignment : steps.length+1=K^d)
    (C mu H alpha tau rho : ℝ) (hC : 0≤C) (hmu : 0≤mu) (hH : 0≤H) (ha : 0≤alpha)
    (htau : 0<tau) (x : Space d)
    (holder : ∀a b,|f b-f a|≤H*‖b-a‖^alpha)
    (bounded : ∀i,i≤steps.length → |f (anchors i)|≤C)
    (scale : mu^alpha≤2*tau)
    (distances : ∀i,i<steps.length → ‖anchors (i+1)-anchors i‖≤mu*(D:ℝ))
    (hamp : D<2^p) (hN : 2*H*(D:ℝ)^alpha+MathCan.CommonGateBound.commonBudget 0 D/2+1/2≤(N:ℝ))
    (hwidth : 2*N<2^a)
    (hdist : ‖x-anchors (snakeRank K (sites.map Site.fine))‖≤rho) :
    |f x-capturedValue f anchors spatialN K D N p a delta C tau sites steps|≤H*rho^alpha+tau/2 := by
  have hr:=holder_residuals steps anchors mu (D:ℝ) H alpha tau hmu (Nat.cast_nonneg D)
    hH ha htau holder scale distances
  have hc:=sharp_decoded_accuracy spatialN K d 1 0 D N p a hK delta hdelta sites dimension safe
    (constantIndex d) hD (fun j l _=>Subsingleton.elim j l) (by intro j axis; exact Nat.le_refl 0)
    hamp C tau (2*H*(D:ℝ)^alpha) hC htau hN hwidth steps valid alignment
    (fun i _=>f (anchors i)) hr (fun i hi _=>abs_le.mp (bounded i hi)) 0
  change |capturedValue f anchors spatialN K D N p a delta C tau sites steps-
    f (anchors (snakeRank K (sites.map Site.fine)))|≤tau/2 at hc
  have hp:=Real.rpow_le_rpow (norm_nonneg (x-anchors (snakeRank K (sites.map Site.fine)))) hdist ha
  have hf:|f x-f (anchors (snakeRank K (sites.map Site.fine)))|≤H*rho^alpha :=
    (holder _ x).trans (mul_le_mul_of_nonneg_left hp hH)
  exact (abs_sub_le (f x) (f (anchors (snakeRank K (sites.map Site.fine)))) _).trans
    (add_le_add hf (by simpa only [abs_sub_comm] using hc))

end MathCan.HolderCapture
