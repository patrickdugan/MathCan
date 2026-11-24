import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory Filter

namespace CLN04

/-- The measure-theoretic engine: summability of expected nonnegative
energies forces the pointwise energies to tend to zero almost surely.
It applies to a fixed finite grid of Weyl sample sizes or a flattened
countable collection of sample sizes. -/
theorem ae_energy_tends_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Ω → ℝ≥0∞)
    (hE : ∀ n, AEMeasurable (E n) μ)
    (hs : (∑' n, ∫⁻ x, E n x ∂μ) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun n => E n x) atTop (𝓝 0) := by
  have htotal : (∫⁻ x, ∑' n, E n x ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hE]
    exact hs
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hE) htotal] with x hx
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne

/-- For a probability measure the pointwise conditional bound
can be integrated without paying any tail-dependent factor.
Here E is the nonnegative conditional energy as a function of tail.
A separate kernel/disintegration lemma identifies it with the actual
conditional expectation in the digit model. -/
theorem average_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → ℝ≥0∞) (B : ℝ≥0∞) (h : ∀ᵐ x ∂μ, E x ≤ B) :
    (∫⁻ x, E x ∂μ) ≤ B := by
  calc
    _ ≤ ∫⁻ _x : Ω, B ∂μ := lintegral_mono_ae h
    _ = B := by simp

/-- Pure filter form of the finite-grid argument. For each epsilon,
the chosen grid approximation G tends to zero and eventually bounds
the target A with that additive epsilon. No specific grid construction
is presumed in this lemma. -/
theorem interpolation_zero (A : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ A n)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ G : ℕ → ℝ, Tendsto G atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, A n ≤ G n + ε) :
    Tendsto A atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha (hnonneg n)
  · intro a ha
    obtain ⟨G, hG, hbound⟩ := happrox (a / 2) (by linarith)
    have hsmall := (tendsto_order.1 hG).2 (a / 2) (by linarith)
    filter_upwards [hbound, hsmall] with n h1 h2
    linarith

#print axioms ae_energy_tends_zero
#print axioms average_tail_bound
#print axioms interpolation_zero

end CLN04
