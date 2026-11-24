import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace CLN06A

section Independent

variable {Ω A T : Type*}
  [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace T]
  [Fintype A] [MeasurableSingletonClass A]

/-- The prefix/tail calculation is an exact product integration
identity when the finite prefix A and tail T are independent.
This statement is about the true pushforward law on one probability
space, so it does not silently replace a joint law by its marginals. -/
theorem independent_prefix_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (prefix : Ω → A) (tail : Ω → T)
    (hp : Measurable prefix) (ht : Measurable tail)
    (hi : IndepFun prefix tail μ)
    (E : A × T → ℝ≥0∞) (hE : Measurable E) :
    (∫⁻ x, E (prefix x, tail x) ∂μ) =
      ∫⁻ t, ∑ a, E (a,t) * (μ.map prefix) {a} ∂μ.map tail := by
  classical
  calc
    _ = ∫⁻ z, E z ∂μ.map (fun x => (prefix x, tail x)) :=
      (lintegral_map hE (hp.prodMk ht)).symm
    _ = ∫⁻ z, E z ∂(μ.map prefix).prod (μ.map tail) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map
        hp.aemeasurable ht.aemeasurable).mp hi]
    _ = ∫⁻ t, ∫⁻ a, E (a,t) ∂μ.map prefix ∂μ.map tail :=
      lintegral_prod_symm' E hE
    _ = _ := by simp_rw [lintegral_fintype]

/-- The uniform-in-tail finite Fourier envelope becomes a global
expectation bound with no additional distribution-dependent constant. -/
theorem independent_prefix_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (prefix : Ω → A) (tail : Ω → T)
    (hp : Measurable prefix) (ht : Measurable tail)
    (hi : IndepFun prefix tail μ)
    (E : A × T → ℝ≥0∞) (hE : Measurable E)
    (B : ℝ≥0∞)
    (hbound : ∀ᵐ t ∂μ.map tail,
      (∑ a, E (a,t) * (μ.map prefix) {a}) ≤ B) :
    (∫⁻ x, E (prefix x, tail x) ∂μ) ≤ B := by
  rw [independent_prefix_integral μ prefix tail hp ht hi E hE]
  calc
    _ ≤ ∫⁻ _t : T, B ∂μ.map tail := lintegral_mono_ae hbound
    _ = B := by
      rw [lintegral_const, Measure.map_apply ht MeasurableSet.univ]
      simp

/-- The same integration identity when independence is unavailable
but the joint law is explicitly a finite mixture of tail measures.
A conditional-law construction must supply this mixture identity. -/
theorem finite_mixture_integral
    (ν : A → Measure T) (w : A → ℝ≥0∞)
    (E : T → ℝ≥0∞) :
    (∫⁻ t, E t ∂Measure.sum (fun a => w a • ν a)) =
      ∑ a, w a * ∫⁻ t, E t ∂ν a := by
  rw [lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul, tsum_fintype]

end Independent

/-- Passing from a countable family of expected-energy bounds to an
almost-sure conclusion can use a shared deterministic summable
majorant. No union over uncountably many tails is required. -/
theorem ae_energy_of_majorant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Ω → ℝ≥0∞) (B : ℕ → ℝ≥0∞)
    (hE : ∀ n, AEMeasurable (E n) μ)
    (hbound : ∀ n, (∫⁻ x, E n x ∂μ) ≤ B n)
    (hB : (∑' n, B n) < ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun n => E n x) atTop (𝓝 0) := by
  have hs : (∑' n, ∫⁻ x, E n x ∂μ) < ∞ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) hB
  have ht : (∫⁻ x, ∑' n, E n x ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hE]
    exact hs.ne
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hE) ht] with x hx
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne

#print axioms independent_prefix_integral
#print axioms independent_prefix_bound
#print axioms finite_mixture_integral
#print axioms ae_energy_of_majorant

end CLN06A
