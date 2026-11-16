import ApproximationMathlib.SmoothTaylor
import MathCan.CommonGateCapture

/-! The scalar polynomial used by the decoder has the analytic Taylor meaning.
Coefficient accuracy is an explicit contract, separate from the proved analytic
remainder and the proved exact spatial/sentinel capture. -/
namespace MathCan.CapturedApproximation
open MathCan.TaylorFoundation MathCan.TaylorPolynomial MathCan.SmoothTaylor
open Set
open scoped Interval Nat

noncomputable def coefficients (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (a : ℝ) : Fin (n+1) → ℝ :=
  fun i=>((i.val)! : ℝ)⁻¹*iteratedDerivWithin i.val f s a

theorem evaluate_ofFn {J : ℕ} (c : Fin J → ℝ) (h : ℝ) :
    evaluate (List.ofFn c) h=∑i:Fin J,c i*h^i.val := by
  induction J with
  | zero => simp [evaluate]
  | succ J ih =>
    rw [List.ofFn_succ,evaluate,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,pow_zero,mul_one,pow_succ]
    simp only [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The previously replayed Horner polynomial is the genuine Taylor polynomial. -/
theorem evaluate_coefficients (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (a x : ℝ) :
    evaluate (List.ofFn (coefficients f n s a)) (x-a)=taylorWithinEval f n s a x := by
  rw [evaluate_ofFn,taylor_within_apply,Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coefficients,smul_eq_mul]
  ring

theorem coefficient_error_bound {J : ℕ} (q c eta : Fin J → ℝ) (h : ℝ)
    (error:∀i,|q i-c i| ≤ eta i) :
    |evaluate (List.ofFn q) h-evaluate (List.ofFn c) h| ≤ ∑i:Fin J,eta i* |h|^i.val := by
  rw [evaluate_ofFn,evaluate_ofFn,← Finset.sum_sub_distrib]
  calc
    _  ≤  ∑i:Fin J,|q i*h^i.val-c i*h^i.val| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑i:Fin J,|q i-c i| * |h|^i.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← sub_mul,abs_mul,abs_pow]
    _  ≤  _ := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (error i) (pow_nonneg (abs_nonneg _) _))

/-- Uniform coordinate quantization costs at most J*epsilon on a unit cell. -/
theorem unit_cell_coefficient_error {J : ℕ} (q c : Fin J → ℝ) (h epsilon : ℝ)
    (hepsilon:0 ≤ epsilon) (hh:|h| ≤ 1) (error:∀i,|q i-c i| ≤ epsilon) :
    |evaluate (List.ofFn q) h-evaluate (List.ofFn c) h| ≤ (J:ℝ)*epsilon := by
  have he:=coefficient_error_bound q c (fun _=>epsilon) h error
  calc
    _  ≤  ∑i:Fin J,epsilon* |h|^i.val := he
    _  ≤  ∑_i:Fin J,epsilon := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_right hepsilon (pow_le_one₀ (abs_nonneg _) hh)
    _ = _ := by simp

/-- A local approximation theorem with an analytic smoothness premise and an
explicit coefficient quantization error; there is no assumed remainder. -/
theorem smooth_approximation {f : ℝ → ℝ} {a x M : ℝ} {n : ℕ}
    (hM:0 ≤ M) (hf:ContDiffOn ℝ (n+1) f (uIcc a x))
    (bound:∀c∈uIcc a x,|iteratedDerivWithin (n+1) f (uIcc a x) c| ≤ M)
    (q eta : Fin (n+1) → ℝ)
    (error:∀i,|q i-coefficients f n (uIcc a x) a i| ≤ eta i) :
    |f x-evaluate (List.ofFn q) (x-a)| ≤ 
      M* |x-a|^(n+1)/(n+1)!+∑i:Fin (n+1),eta i* |x-a|^i.val := by
  have hr:=smooth_remainder_bound hM hf bound
  have he:=coefficient_error_bound q (coefficients f n (uIcc a x) a) eta (x-a) error
  rw [evaluate_coefficients] at he
  rw [abs_sub_comm] at he
  exact le_trans (abs_sub_le (f x) (taylorWithinEval f n (uIcc a x) a x)
    (evaluate (List.ofFn q) (x-a))) (add_le_add hr he)

/-- Hölder regularity gives the corresponding noninteger local rate. -/
theorem holder_approximation {f : ℝ → ℝ} {a x H alpha : ℝ} {n : ℕ}
    (hH:0 ≤ H) (ha:0 ≤ alpha) (hf:ContDiffOn ℝ (n+1) f (uIcc a x))
    (holder:∀c∈uIcc a x,|iteratedDerivWithin (n+1) f (uIcc a x) c-
      iteratedDerivWithin (n+1) f (uIcc a x) a| ≤ H* |c-a|^alpha)
    (q eta : Fin (n+2) → ℝ)
    (error:∀i,|q i-coefficients f (n+1) (uIcc a x) a i| ≤ eta i) :
    |f x-evaluate (List.ofFn q) (x-a)| ≤ 
      H* |x-a|^(((n+1:ℕ):ℝ)+alpha)/(n+1)!+∑i:Fin (n+2),eta i* |x-a|^i.val := by
  have hr:=holder_remainder_bound hH ha hf holder
  have he:=coefficient_error_bound q (coefficients f (n+1) (uIcc a x) a) eta (x-a) error
  rw [evaluate_coefficients] at he
  rw [abs_sub_comm] at he
  exact le_trans (abs_sub_le (f x) (taylorWithinEval f (n+1) (uIcc a x) a x)
    (evaluate (List.ofFn q) (x-a))) (add_le_add hr he)

/-- Explicit local grid rate for smooth functions and uniformly quantized
Taylor coefficients. The constants depend on degree, not on stream length. -/
theorem smooth_uniform_approximation {f : ℝ → ℝ} {a x M rho epsilon : ℝ} {n : ℕ}
    (hM:0 ≤ M) (hrho:rho ≤ 1) (hdist:|x-a| ≤ rho) (hepsilon:0 ≤ epsilon)
    (hf:ContDiffOn ℝ (n+1) f (uIcc a x))
    (bound:∀c∈uIcc a x,|iteratedDerivWithin (n+1) f (uIcc a x) c| ≤ M)
    (q : Fin (n+1) → ℝ)
    (error:∀i,|q i-coefficients f n (uIcc a x) a i| ≤ epsilon) :
    |f x-evaluate (List.ofFn q) (x-a)| ≤ M*rho^(n+1)/(n+1)!+((n+1:ℕ):ℝ)*epsilon := by
  have hr:=smooth_remainder_bound hM hf bound
  have hp:=pow_le_pow_left₀ (abs_nonneg (x-a)) hdist (n+1)
  have hb:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hM) (Nat.cast_nonneg ((n+1)!))
  have he:=unit_cell_coefficient_error q (coefficients f n (uIcc a x) a) (x-a) epsilon
    hepsilon (le_trans hdist hrho) error
  rw [evaluate_coefficients,abs_sub_comm] at he
  exact le_trans (abs_sub_le (f x) (taylorWithinEval f n (uIcc a x) a x)
    (evaluate (List.ofFn q) (x-a))) (add_le_add (le_trans hr hb) he)

/-- The corresponding fractional grid rate for a Hölder highest derivative. -/
theorem holder_uniform_approximation {f : ℝ → ℝ} {a x H alpha rho epsilon : ℝ} {n : ℕ}
    (hH:0 ≤ H) (ha:0 ≤ alpha) (hrho:rho ≤ 1) (hdist:|x-a| ≤ rho) (hepsilon:0 ≤ epsilon)
    (hf:ContDiffOn ℝ (n+1) f (uIcc a x))
    (holder:∀c∈uIcc a x,|iteratedDerivWithin (n+1) f (uIcc a x) c-
      iteratedDerivWithin (n+1) f (uIcc a x) a| ≤ H* |c-a|^alpha)
    (q : Fin (n+2) → ℝ)
    (error:∀i,|q i-coefficients f (n+1) (uIcc a x) a i| ≤ epsilon) :
    |f x-evaluate (List.ofFn q) (x-a)| ≤ 
      H*rho^(((n+1:ℕ):ℝ)+alpha)/(n+1)!+((n+2:ℕ):ℝ)*epsilon := by
  have hr:=holder_remainder_bound hH ha hf holder
  have hp:=Real.rpow_le_rpow (abs_nonneg (x-a)) hdist (show 0 ≤ ((n+1:ℕ):ℝ)+alpha by positivity)
  have hb:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hH) (Nat.cast_nonneg ((n+1)!))
  have he:=unit_cell_coefficient_error q (coefficients f (n+1) (uIcc a x) a) (x-a) epsilon
    hepsilon (le_trans hdist hrho) error
  rw [evaluate_coefficients,abs_sub_comm] at he
  exact le_trans (abs_sub_le (f x) (taylorWithinEval f (n+1) (uIcc a x) a x)
    (evaluate (List.ofFn q) (x-a))) (add_le_add (le_trans hr hb) he)

open MathCan.SpatialScalar MathCan.SpatialNormalized MathCan.SpatialRouting
open MathCan.SpatialClipped MathCan.TaylorFrame MathCan.ConcreteJetCapture
open MathCan.SentinelDecoder MathCan.CommonGateCapture

noncomputable def capturedCoefficients {d J : ℕ} (spatialN K k D p width : ℕ)
    (delta : ℝ) (sites : List (Site ℝ)) (indices : Fin J → Fin d → ℕ)
    (C centre tau : ℝ) (frames : List (Frame d J)) (initial : Fin J → ℝ) : Fin J → ℝ :=
  fun beta=>captureStream C
    (((K^d:ℕ):ℝ)*clippedCircuit K (decodedDigits spatialN K delta sites))
    (fun j=>commonScheduledAt indices k D p width C centre tau (schedule frames)
      (word (codePayload p width frames)) initial j beta) (K^d)

/-- Exact common-bound decoded spatial capture feeds an analytic approximation
bound. Coefficient accuracy is the remaining quantized-jet synthesis contract;
the smooth Taylor remainder and the complete decoder are proved here. -/
theorem decoded_smooth_approximation (spatialN K d n k D p width : ℕ)
    (hK:0<K) (delta : ℝ) (hdelta:0<delta) (sites : List (Site ℝ))
    (dimension:sites.length=d) (safe:validSites spatialN K delta sites)
    (indices : Fin (n+1) → Fin d → ℕ) (hD:1 ≤ D)
    (injective:∀j l,indices j=indices l → j=l) (degree:∀gamma j,indices gamma j ≤ k)
    (hwidth:D<2^p) (C centre tau : ℝ) (hC:0 ≤ C) (frames : List (Frame d (n+1)))
    (valid:∀f,f∈frames → validFrame D width f) (alignment:frames.length+1=K^d)
    (initial : Fin (n+1) → ℝ) (hinit:∀beta,-C ≤ initial beta ∧ initial beta ≤ C)
    (f : ℝ → ℝ) (anchor : ℕ → ℝ) (x M : ℝ) (hM:0 ≤ M) (eta : Fin (n+1) → ℝ)
    (smooth:∀j,j ≤ frames.length → ContDiffOn ℝ (n+1) f (uIcc (anchor j) x))
    (derivative:∀j,j ≤ frames.length → ∀c∈uIcc (anchor j) x,
      |iteratedDerivWithin (n+1) f (uIcc (anchor j) x) c| ≤ M)
    (accuracy:∀j,j ≤ frames.length → ∀i,
      |referenceAt indices C centre tau frames initial j i-
        coefficients f n (uIcc (anchor j) x) (anchor j) i| ≤ eta i) :
    let r:=snakeRank K (sites.map Site.fine)
    |f x-evaluate (List.ofFn (capturedCoefficients spatialN K k D p width delta sites indices
      C centre tau frames initial)) (x-anchor r)| ≤ 
      M* |x-anchor r|^(n+1)/(n+1)!+∑i:Fin (n+1),eta i* |x-anchor r|^i.val := by
  dsimp only
  have hc:=common_spatial_capture spatialN K d (n+1) hK delta hdelta sites dimension safe
    indices k D p width hD injective degree hwidth C centre tau hC frames valid alignment initial hinit
  have heq:capturedCoefficients spatialN K k D p width delta sites indices C centre tau frames initial=
      referenceAt indices C centre tau frames initial (snakeRank K (sites.map Site.fine)):=hc.2
  rw [heq]
  exact smooth_approximation hM (smooth _ hc.1) (derivative _ hc.1) _ eta (accuracy _ hc.1)

/-- The same decoded-capture connection for fractional smoothness. -/
theorem decoded_holder_approximation (spatialN K d n k D p width : ℕ)
    (hK:0<K) (delta : ℝ) (hdelta:0<delta) (sites : List (Site ℝ))
    (dimension:sites.length=d) (safe:validSites spatialN K delta sites)
    (indices : Fin (n+2) → Fin d → ℕ) (hD:1 ≤ D)
    (injective:∀j l,indices j=indices l → j=l) (degree:∀gamma j,indices gamma j ≤ k)
    (hwidth:D<2^p) (C centre tau : ℝ) (hC:0 ≤ C) (frames : List (Frame d (n+2)))
    (valid:∀f,f∈frames → validFrame D width f) (alignment:frames.length+1=K^d)
    (initial : Fin (n+2) → ℝ) (hinit:∀beta,-C ≤ initial beta ∧ initial beta ≤ C)
    (f : ℝ → ℝ) (anchor : ℕ → ℝ) (x H alpha : ℝ) (hH:0 ≤ H) (ha:0 ≤ alpha) (eta : Fin (n+2) → ℝ)
    (smooth:∀j,j ≤ frames.length → ContDiffOn ℝ (n+1) f (uIcc (anchor j) x))
    (holder:∀j,j ≤ frames.length → ∀c∈uIcc (anchor j) x,
      |iteratedDerivWithin (n+1) f (uIcc (anchor j) x) c-
        iteratedDerivWithin (n+1) f (uIcc (anchor j) x) (anchor j)| ≤ H* |c-anchor j|^alpha)
    (accuracy:∀j,j ≤ frames.length → ∀i,
      |referenceAt indices C centre tau frames initial j i-
        coefficients f (n+1) (uIcc (anchor j) x) (anchor j) i| ≤ eta i) :
    let r:=snakeRank K (sites.map Site.fine)
    |f x-evaluate (List.ofFn (capturedCoefficients spatialN K k D p width delta sites indices
      C centre tau frames initial)) (x-anchor r)| ≤ 
      H* |x-anchor r|^(((n+1:ℕ):ℝ)+alpha)/(n+1)!+∑i:Fin (n+2),eta i* |x-anchor r|^i.val := by
  dsimp only
  have hc:=common_spatial_capture spatialN K d (n+2) hK delta hdelta sites dimension safe
    indices k D p width hD injective degree hwidth C centre tau hC frames valid alignment initial hinit
  have heq:capturedCoefficients spatialN K k D p width delta sites indices C centre tau frames initial=
      referenceAt indices C centre tau frames initial (snakeRank K (sites.map Site.fine)):=hc.2
  rw [heq]
  exact holder_approximation hH ha (smooth _ hc.1) (holder _ hc.1) _ eta (accuracy _ hc.1)

/-- A uniform fractional approximation rate for the actual common-bound
Hamming/sentinel/spatial capture circuit, conditional on coefficient accuracy. -/
theorem decoded_holder_uniform_approximation (spatialN K d n k D p width : ℕ)
    (hK:0<K) (delta : ℝ) (hdelta:0<delta) (sites : List (Site ℝ))
    (dimension:sites.length=d) (safe:validSites spatialN K delta sites)
    (indices : Fin (n+2) → Fin d → ℕ) (hD:1 ≤ D)
    (injective:∀j l,indices j=indices l → j=l) (degree:∀gamma j,indices gamma j ≤ k)
    (hwidth:D<2^p) (C centre tau : ℝ) (hC:0 ≤ C) (frames : List (Frame d (n+2)))
    (valid:∀f,f∈frames → validFrame D width f) (alignment:frames.length+1=K^d)
    (initial : Fin (n+2) → ℝ) (hinit:∀beta,-C ≤ initial beta ∧ initial beta ≤ C)
    (f : ℝ → ℝ) (anchor : ℕ → ℝ) (x H alpha rho epsilon : ℝ) (hH:0 ≤ H) (ha:0 ≤ alpha) (hrho:rho ≤ 1) (hepsilon:0 ≤ epsilon)
    (hdist:∀j,j ≤ frames.length → |x-anchor j| ≤ rho)
    (smooth:∀j,j ≤ frames.length → ContDiffOn ℝ (n+1) f (uIcc (anchor j) x))
    (holder:∀j,j ≤ frames.length → ∀c∈uIcc (anchor j) x,
      |iteratedDerivWithin (n+1) f (uIcc (anchor j) x) c-
        iteratedDerivWithin (n+1) f (uIcc (anchor j) x) (anchor j)| ≤ H* |c-anchor j|^alpha)
    (accuracy:∀j,j ≤ frames.length → ∀i,
      |referenceAt indices C centre tau frames initial j i-
        coefficients f (n+1) (uIcc (anchor j) x) (anchor j) i| ≤ epsilon) :
    let r:=snakeRank K (sites.map Site.fine)
    |f x-evaluate (List.ofFn (capturedCoefficients spatialN K k D p width delta sites indices
      C centre tau frames initial)) (x-anchor r)| ≤ 
      H*rho^(((n+1:ℕ):ℝ)+alpha)/(n+1)!+((n+2:ℕ):ℝ)*epsilon := by
  dsimp only
  have hc:=common_spatial_capture spatialN K d (n+2) hK delta hdelta sites dimension safe
    indices k D p width hD injective degree hwidth C centre tau hC frames valid alignment initial hinit
  have heq:capturedCoefficients spatialN K k D p width delta sites indices C centre tau frames initial=
      referenceAt indices C centre tau frames initial (snakeRank K (sites.map Site.fine)):=hc.2
  rw [heq]
  exact holder_uniform_approximation hH ha hrho (hdist _ hc.1) hepsilon (smooth _ hc.1) (holder _ hc.1) _ (accuracy _ hc.1)

end MathCan.CapturedApproximation
