import ApproximationMathlib.FrameSynthesis
import MathCan.CommonGateCapture

/-! Decoded spatial coefficient accuracy for synthesized correction frames. -/
namespace MathCan.SynthesisCapture
open MathCan.FrameSynthesis MathCan.JetSynthesis MathCan.TaylorFrame
open MathCan.ConcreteJetCapture MathCan.CommonGateCapture MathCan.CommonGateBound
open MathCan.SpatialScalar MathCan.SpatialNormalized MathCan.SpatialRouting
open MathCan.CapturedApproximation
set_option autoImplicit false

theorem reference_accuracy {d J : ℕ} (indices : Fin J → Fin d → ℕ) (k D N a : ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (C tau : ℝ) (hC : 0≤C) (htau : 0<tau)
    (hN : (C+C*commonBudget k D)/tau+1/2≤(N:ℝ)) (hwidth : 2*N<2^a)
    (steps : List (Step d)) (valid : ∀s,s∈steps → s.magnitude≤D)
    (targets : ℕ → Fin J → ℝ)
    (bounded : ∀i,i≤steps.length → ∀beta,-C≤targets i beta ∧ targets i beta≤C) :
    ∀i,i≤steps.length → ∀beta,
      |referenceAt indices C (N:ℝ) tau
        (frames indices N C tau steps targets (initial C tau (targets 0)))
        (initial C tau (targets 0)) i beta-targets i beta|≤tau/2 := by
  have hs:=frames_valid_exact indices k D N a hD injective degree C tau hC htau hN hwidth
    steps valid targets bounded (initial C tau (targets 0)) (initial_range C tau hC _)
  intro i hi beta
  rw [hs.2 i]
  exact states_accuracy indices C tau hC htau steps targets bounded _
    (initial_accuracy C tau hC htau _ (bounded 0 (by omega))) i hi beta

theorem decoded_coefficient_accuracy (spatialN K d J k D N p a : ℕ) (hK : 0<K)
    (delta : ℝ) (hdelta : 0<delta) (sites : List (Site ℝ)) (dimension : sites.length=d)
    (safe : validSites spatialN K delta sites) (indices : Fin J → Fin d → ℕ)
    (hD : 1≤D) (injective : ∀j l,indices j=indices l → j=l)
    (degree : ∀j axis,indices j axis≤k) (hamp : D<2^p)
    (C tau : ℝ) (hC : 0≤C) (htau : 0<tau)
    (hN : (C+C*commonBudget k D)/tau+1/2≤(N:ℝ)) (hwidth : 2*N<2^a)
    (steps : List (Step d)) (valid : ∀s,s∈steps → s.magnitude≤D)
    (alignment : steps.length+1=K^d) (targets : ℕ → Fin J → ℝ)
    (bounded : ∀i,i≤steps.length → ∀beta,-C≤targets i beta ∧ targets i beta≤C) :
    ∀beta,|capturedCoefficients spatialN K k D p a delta sites indices C (N:ℝ) tau
      (frames indices N C tau steps targets (initial C tau (targets 0)))
      (initial C tau (targets 0)) beta-targets (snakeRank K (sites.map Site.fine)) beta|≤tau/2 := by
  let v:=initial C tau (targets 0)
  have hs:=frames_valid_exact indices k D N a hD injective degree C tau hC htau hN hwidth
    steps valid targets bounded v (initial_range C tau hC _)
  have hc:=common_spatial_capture spatialN K d J hK delta hdelta sites dimension safe indices
    k D p a hD injective degree hamp C (N:ℝ) tau hC (frames indices N C tau steps targets v)
    hs.1 (by rw [frames_length]; exact alignment) v (initial_range C tau hC _)
  have hr:snakeRank K (sites.map Site.fine)≤steps.length:=by simpa only [frames_length] using hc.1
  have he:capturedCoefficients spatialN K k D p a delta sites indices C (N:ℝ) tau
      (frames indices N C tau steps targets v) v=
      referenceAt indices C (N:ℝ) tau (frames indices N C tau steps targets v) v
        (snakeRank K (sites.map Site.fine)):=hc.2
  rw [he]
  exact reference_accuracy indices k D N a hD injective degree C tau hC htau hN hwidth steps valid targets bounded _ hr

end MathCan.SynthesisCapture
