import ApproximationMathlib.MultivariateBounds
import ApproximationMathlib.MultivariateHolder
import ApproximationMathlib.SynthesisCapture

/-! Full coefficient synthesis to decoded multivariate approximation. The
coefficient-accuracy hypothesis of the preceding checkpoint is now a theorem.
The correction alphabet is finite and uses the explicit general predictor bound. -/
namespace MathCan.MultivariateCapture
open MathCan.MultivariateTaylor MathCan.MultivariateBounds MathCan.MultivariateHolder
open MathCan.JetSynthesis MathCan.FrameSynthesis MathCan.SynthesisCapture
open MathCan.CommonGateBound
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
    (M tau : ℝ) (hM : 0≤M) (htau : 0<tau)
    (jetBound : ∀i,i≤steps.length → ∀n,n≤k → ‖iteratedFDeriv ℝ n f (anchors i)‖≤M)
    (hamp : D<2^p) (hN : (budget d k*M+(budget d k*M)*commonBudget k D)/tau+1/2≤(N:ℝ))
    (hwidth : 2*N<2^a) :
    ∀beta,|capturedJet f k anchors spatialN K D N p a delta (budget d k*M) tau sites steps beta-
      coefficients f k (anchors (snakeRank K (sites.map Site.fine))) beta|≤tau/2 := by
  have bounded:∀i,i≤steps.length → ∀beta,
      -(budget d k*M)≤targets f k anchors i beta ∧ targets f k anchors i beta≤budget d k*M := by
    intro i hi beta
    exact abs_le.mp (coefficients_bound (anchors i) M hM (jetBound i hi) beta)
  exact decoded_coefficient_accuracy spatialN K d (size d k) k D N p a hK delta hdelta sites dimension safe
    (labels d k) hD (fun j l he=>labels_injective d k he) (labels_degree d k) hamp (budget d k*M) tau
    (mul_nonneg (budget_nonneg d k) hM) htau hN hwidth steps valid alignment (targets f k anchors) bounded

theorem smooth_decoded_approximation {d n : ℕ} {f : Space d→ℝ} (hf : ContDiff ℝ (n+1) f)
    (anchors : ℕ→Space d) (spatialN K D N p a : ℕ) (hK : 0<K) (hD : 1≤D)
    (delta : ℝ) (hdelta : 0<delta) (sites : List (Site ℝ)) (dimension : sites.length=d)
    (safe : validSites spatialN K delta sites) (steps : List (Step d))
    (valid : ∀s,s∈steps → s.magnitude≤D) (alignment : steps.length+1=K^d)
    (M tau rho : ℝ) (hM : 0≤M) (htau : 0<tau) (hrho : rho≤1) (x : Space d)
    (jetBound : ∀i,i≤steps.length → ∀j,j≤n → ‖iteratedFDeriv ℝ j f (anchors i)‖≤M)
    (hamp : D<2^p) (hN : (budget d n*M+(budget d n*M)*commonBudget n D)/tau+1/2≤(N:ℝ))
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
      steps valid alignment M tau hM htau jetBound hamp hN hwidth)

theorem holder_decoded_approximation {d n : ℕ} {f : Space d→ℝ} (hf : ContDiff ℝ (n+1) f)
    (anchors : ℕ→Space d) (spatialN K D N p a : ℕ) (hK : 0<K) (hD : 1≤D)
    (delta : ℝ) (hdelta : 0<delta) (sites : List (Site ℝ)) (dimension : sites.length=d)
    (safe : validSites spatialN K delta sites) (steps : List (Step d))
    (valid : ∀s,s∈steps → s.magnitude≤D) (alignment : steps.length+1=K^d)
    (M H alpha tau rho : ℝ) (hM : 0≤M) (hH : 0≤H) (ha : 0≤alpha) (htau : 0<tau) (hrho : rho≤1) (x : Space d)
    (jetBound : ∀i,i≤steps.length → ∀j,j≤n+1 → ‖iteratedFDeriv ℝ j f (anchors i)‖≤M)
    (hamp : D<2^p)
    (hN : (budget d (n+1)*M+(budget d (n+1)*M)*commonBudget (n+1) D)/tau+1/2≤(N:ℝ))
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
      steps valid alignment M tau hM htau jetBound hamp hN hwidth)

theorem finite_frame_parameters (B : ℝ) (D : ℕ) :
    ∃N p a:ℕ,B+1/2≤(N:ℝ) ∧ D<2^p ∧ 2*N<2^a := by
  obtain ⟨N,hN⟩:=exists_nat_gt (B+1/2)
  exact ⟨N,D,2*N,hN.le,by exact Nat.lt_two_pow_self,by exact Nat.lt_two_pow_self⟩

end MathCan.MultivariateCapture
