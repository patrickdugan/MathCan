import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Closure
import Mathlib.Tactic

/-!
# DEL-08: preserving closed immersions and normalizing the fixed coefficient

The graph-coordinate lemma is a genuine affine-scheme result:
a surjective coordinate-ring map stays surjective after adjoining
one freely variable coordinate and assigning it any function b.
The induced morphism of affine schemes is a closed immersion.

The dense-chart lemma is a general topological consequence of
two dense opens and the nonempty principal chart. Existence of the
actual Zariski opens from Bertini and Katz is an external geometric
input. Extension-field descent is treated separately.
-/

open scoped BigOperators
open Finset

namespace Deligne08

/-- Graphing an arbitrary extra regular function preserves a
surjective affine coordinate-ring map. -/
theorem graph_coordinate_surjective
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (b : B) :
    Function.Surjective (Polynomial.eval₂RingHom f b) := by
  intro z
  obtain ⟨a, ha⟩ := hf z
  refine ⟨Polynomial.C a, ?_⟩
  simpa using ha

/-- A scheme-theoretic graph embedding into one extra affine
coordinate remains a closed immersion. This is the affine-scheme
translation of the preceding ring-surjectivity theorem. -/
theorem graph_closed_immersion
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (b : B) :
    AlgebraicGeometry.IsClosedImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Polynomial.eval₂RingHom f b))) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (graph_coordinate_surjective f hf b)

/-- The affine family of hyperplanes pulled back along coordinates
(z_1,...,z_s,b), where b is the fixed regular function. -/
def hyperplaneEquation {K : Type*} [CommRing K] {s : ℕ}
    (a : Fin s → K) (lambda c b : K) (z : Fin s → K) : K :=
  (∑ i : Fin s, a i * z i) + lambda * b + c

/-- Hyperplane equations after setting the coefficient on b to 1. -/
def fixedCoefficientEquation {K : Type*} [CommRing K] {s : ℕ}
    (a : Fin s → K) (c b : K) (z : Fin s → K) : K :=
  (∑ i : Fin s, a i * z i) + b + c

/-- In the projective chart lambda != 0, the hyperplane equation
is lambda times the unique equation with coefficient on b equal to 1. -/
theorem hyperplane_normalization
    {K : Type*} [Field K] {s : ℕ}
    (a : Fin s → K) (lambda c b : K) (z : Fin s → K)
    (hlambda : lambda ≠ 0) :
    hyperplaneEquation a lambda c b z =
      lambda * fixedCoefficientEquation
        (fun i => a i / lambda) (c / lambda) b z := by
  have cancel (x : K) : lambda * (x / lambda) = x := by
    field_simp [hlambda]
  have sum_cancel :
      lambda * (∑ i : Fin s, (a i / lambda) * z i) =
        ∑ i : Fin s, a i * z i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      lambda * ((a i / lambda) * z i) =
          (lambda * (a i / lambda)) * z i := by ring
      _ = a i * z i := by rw [cancel]
  dsimp [hyperplaneEquation, fixedCoefficientEquation]
  calc
    (∑ i : Fin s, a i * z i) + lambda * b + c =
        lambda * (∑ i : Fin s, (a i / lambda) * z i) +
          lambda * b + lambda * (c / lambda) := by
            rw [sum_cancel, cancel]
    _ = lambda *
      ((∑ i : Fin s, (a i / lambda) * z i) + b + c / lambda) := by
            ring

/-- The zero loci of the original hyperplane and normalized
fixed-coefficient equation agree in the chart lambda != 0. -/
theorem hyperplane_zero_iff_fixed
    {K : Type*} [Field K] {s : ℕ}
    (a : Fin s → K) (lambda c b : K) (z : Fin s → K)
    (hlambda : lambda ≠ 0) :
    hyperplaneEquation a lambda c b z = 0 ↔
      fixedCoefficientEquation
        (fun i => a i / lambda) (c / lambda) b z = 0 := by
  rw [hyperplane_normalization a lambda c b z hlambda]
  simp [hlambda]

/-- A dense weak-Lefschetz open and a dense Bertini-smooth open
meet the nonempty fixed-coefficient parameter chart. -/
theorem good_hyperplane_in_fixed_chart
    {X : Type*} [TopologicalSpace X]
    (smooth lefschetz chart : Set X)
    (hsmooth : Dense smooth) (hlefschetz : Dense lefschetz)
    (hosmooth : IsOpen smooth) (hochart : IsOpen chart)
    (hnchart : chart.Nonempty) :
    ∃ H : X, H ∈ smooth ∧ H ∈ lefschetz ∧ H ∈ chart := by
  have hgood : Dense (smooth ∩ lefschetz) :=
    hsmooth.inter_of_isOpen_left hlefschetz hosmooth
  obtain ⟨H, hH, hc⟩ :=
    hgood.exists_mem_open hochart hnchart
  exact ⟨H, hH.1, hH.2, hc⟩

/-- The dimension count for tangent hyperplanes when the ambient
projective dimension M exceeds the embedded dimension D. This
formalizes the arithmetic of the incidence bound, while its
geometric fiber-dimension premise remains external. -/
theorem tangent_incidence_arithmetic (D M : ℕ)
    (hD : D < M) :
    D + (M - D - 1) = M - 1 ∧ M - 1 < M := by
  omega

#print axioms graph_coordinate_surjective
#print axioms graph_closed_immersion
#print axioms hyperplane_normalization
#print axioms hyperplane_zero_iff_fixed
#print axioms good_hyperplane_in_fixed_chart
#print axioms tangent_incidence_arithmetic

end Deligne08
