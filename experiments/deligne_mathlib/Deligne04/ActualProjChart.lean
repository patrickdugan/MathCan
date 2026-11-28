import Deligne04.ProjectiveQuasiFinite
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Tactic

/-!
# DEL-09: quasi-finiteness of the graph into an actual Proj chart

Mathlib constructs the affine Proj basic-open immersion
    Proj.awayι : Spec (Away(graded ring,f))_0 -> Proj(graded ring).
It is an actual SCHEME morphism, not an abstract chart variable.

For a projective polynomial coordinate system, the degree-zero ring
of the standard chart is isomorphic to the polynomial coordinate ring.
This file represents that necessary coordinate-ring equivalence by an
explicit *scheme isomorphism* coordIso, then proves the graph into the
actual Proj scheme is locally quasi-finite.

A future theorem must construct coordIso for the specific graded
polynomial ring of projective space. The proof does not conflate
an arbitrary graded-ring chart with A^N.
-/

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Deligne09

universe u v

/-- A graph closed immersion followed by an identified genuine basic
open in Proj has the required locally quasi-finite property.

The identification of Spec A[T] with the degree-zero homogeneous
localization chart is an explicit scheme-isomorphism input. -/
theorem graph_into_actual_proj_chart_locallyQuasiFinite
    {A B : Type u} [CommRing A] [CommRing B]
    {R : Type u} [CommRing R]
    {σ : Type v} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (h : R) {d : ℕ} (h_deg : h ∈ 𝒜 d) (hd : 0 < d)
    (coordIso :
      Spec (CommRingCat.of (Polynomial A)) ≅ Spec ↧(Away 𝒜 h))
    (f : A →+* B) (hf : Function.Surjective f) (b : B) :
    LocallyQuasiFinite
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f b)) ≫
        (coordIso.hom ≫ Proj.awayι 𝒜 h h_deg hd)) := by
  haveI : IsOpenImmersion
      (coordIso.hom ≫ Proj.awayι 𝒜 h h_deg hd) := by
    infer_instance
  exact graph_then_chart_locallyQuasiFinite f hf b
    (coordIso.hom ≫ Proj.awayι 𝒜 h h_deg hd)

/-- The same chart composite is locally of finite type, as required
in the scheme-theoretic formulation of quasi-finite morphisms. -/
theorem graph_into_actual_proj_chart_locallyFiniteType
    {A B : Type u} [CommRing A] [CommRing B]
    {R : Type u} [CommRing R]
    {σ : Type v} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (h : R) {d : ℕ} (h_deg : h ∈ 𝒜 d) (hd : 0 < d)
    (coordIso :
      Spec (CommRingCat.of (Polynomial A)) ≅ Spec ↧(Away 𝒜 h))
    (f : A →+* B) (hf : Function.Surjective f) (b : B) :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f b)) ≫
        (coordIso.hom ≫ Proj.awayι 𝒜 h h_deg hd)) := by
  haveI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f b))) :=
    Deligne08.graph_closed_immersion f hf b
  haveI : IsOpenImmersion
      (coordIso.hom ≫ Proj.awayι 𝒜 h h_deg hd) := by
    infer_instance
  exact closed_then_open_locallyFiniteType _
    (coordIso.hom ≫ Proj.awayι 𝒜 h h_deg hd)

#print axioms graph_into_actual_proj_chart_locallyQuasiFinite
#print axioms graph_into_actual_proj_chart_locallyFiniteType

end Deligne09
