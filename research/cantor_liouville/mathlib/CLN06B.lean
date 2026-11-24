import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CLN06B

/-- Coordinates of a countable product of digit probability spaces
are jointly independent. The finite-bit law is instantiated separately. -/
theorem independent_product_coordinates {ι β : Type*}
    [MeasurableSpace β] (ν : ι → Measure β)
    [∀ i, IsProbabilityMeasure (ν i)] :
    iIndepFun (fun i (ω : ι → β) => ω i) (Measure.infinitePi ν) := by
  simpa only [id_eq] using
    (iIndepFun_infinitePi (P := ν) (X := fun _ => id)
      (fun _ => measurable_id))

/-- Disjoint digit blocks stay independent after measurable encodings,
including an infinite tail represented by a convergent measurable sum. -/
theorem independent_block_maps {ι Ω β A T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    [MeasurableSpace A] [MeasurableSpace T]
    (μ : Measure Ω) (f : ι → Ω → β)
    (hi : iIndepFun f μ) (hf : ∀ i, Measurable (f i))
    (S U : Set ι) (hdis : Disjoint S U)
    (F : (S → β) → A) (G : (U → β) → T)
    (hF : Measurable F) (hG : Measurable G) :
    IndepFun (fun ω => F (fun i : S => f i ω))
      (fun ω => G (fun i : U => f i ω)) μ := by
  simpa only [Function.comp_apply] using
    (iIndepFun.indepFun_set S U hdis hi hf).comp hF hG

/-- Each finite assignment of s independent fair bits has
probability exactly (1/2)^s, irrespective of the locations of the bits. -/
theorem fair_cylinder_mass {ι Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) (f : ι → Ω → β) (hi : iIndepFun f μ)
    (S : Finset ι) (a : ι → β)
    (hfair : ∀ i ∈ S, μ (f i ⁻¹' {a i}) = (1/2 : ℝ≥0∞)) :
    μ (⋂ i ∈ S, f i ⁻¹' {a i}) = (1/2 : ℝ≥0∞)^S.card := by
  classical
  calc
    _ = ∏ i ∈ S, μ (f i ⁻¹' {a i}) :=
      hi.measure_inter_preimage_eq_mul S
        (sets := fun i => {a i}) (fun i _ => measurableSet_singleton (a i))
    _ = ∏ _i ∈ S, (1/2 : ℝ≥0∞) :=
      Finset.prod_congr rfl hfair
    _ = _ := by simp

end CLN06B

#print axioms CLN06B.independent_product_coordinates
#print axioms CLN06B.independent_block_maps
#print axioms CLN06B.fair_cylinder_mass
