import Deligne04.FixedCoefficientChart
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Tactic

/-!
# DEL-09: closed graph plus projective affine chart is quasi-finite

Katz A.5 requires a quasi-finite map X -> P^M. The graph constructed
in DEL-08 is a closed immersion into A^M. The standard affine chart
A^M -> P^M is an open immersion and quasi-compact.

This file proves the composition property as an ACTUAL scheme theorem:
the graph followed by any open-immersion chart is an immersion and
locally quasi-finite. If the chart is quasi-compact, the composite is
quasi-compact and has finite fibers. We retain the chart's
open-immersion and quasi-compact properties as EXPLICIT assumptions,
rather than silently constructing the standard projective chart.
-/

open CategoryTheory
open AlgebraicGeometry

namespace Deligne09

universe u

/-- A closed immersion followed by an open immersion has
the locally quasi-finite property required in Katz's theorem. -/
theorem closed_then_open_locallyQuasiFinite
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    LocallyQuasiFinite (i ≫ j) := by
  infer_instance

/-- If the chosen open chart is quasi-compact, the composite is
quasi-compact as well: this is the additional finite-fiber condition. -/
theorem closed_then_open_quasiCompact
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j] :
    QuasiCompact (i ≫ j) := by
  infer_instance

/-- The composite is also locally of finite type, a hypothesis
of the scheme-theoretic meaning of quasi-finiteness. -/
theorem closed_then_open_locallyFiniteType
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    LocallyOfFiniteType (i ≫ j) := by
  infer_instance

/-- A locally quasi-finite and quasi-compact composite has finite
point fibers, without assuming that it is a finite morphism. -/
theorem closed_then_open_finite_fibers
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (z : Z) :
    ((i ≫ j) ⁻¹' ({z} : Set Z)).Finite := by
  haveI : LocallyQuasiFinite (i ≫ j) :=
    closed_then_open_locallyQuasiFinite i j
  haveI : QuasiCompact (i ≫ j) :=
    closed_then_open_quasiCompact i j
  exact (i ≫ j).finite_preimage_singleton z

/-- Application to the actual graph morphism from DEL-08:
adding a prescribed coordinate b to the affine closed immersion
does not destroy the quasi-finiteness of the projective map. -/
theorem graph_then_chart_locallyQuasiFinite
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (b : B)
    {P : Scheme.{u}}
    (chart : Spec (CommRingCat.of (Polynomial A)) ⟶ P)
    [IsOpenImmersion chart] :
    LocallyQuasiFinite
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f b)) ≫ chart) := by
  haveI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f b))) :=
    Deligne08.graph_closed_immersion f hf b
  exact closed_then_open_locallyQuasiFinite _ chart

/-- A quasi-compact projective affine chart produces actual
finite point fibers for the graph's composed map. -/
theorem graph_then_chart_finite_fibers
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (b : B)
    {P : Scheme.{u}}
    (chart : Spec (CommRingCat.of (Polynomial A)) ⟶ P)
    [IsOpenImmersion chart] [QuasiCompact chart]
    (z : P) :
    (((Spec.map
      (CommRingCat.ofHom (Polynomial.eval₂RingHom f b))) ≫ chart)
        ⁻¹' ({z} : Set P)).Finite := by
  haveI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f b))) :=
    Deligne08.graph_closed_immersion f hf b
  exact closed_then_open_finite_fibers _ chart z

#print axioms closed_then_open_locallyQuasiFinite
#print axioms closed_then_open_quasiCompact
#print axioms closed_then_open_locallyFiniteType
#print axioms closed_then_open_finite_fibers
#print axioms graph_then_chart_locallyQuasiFinite
#print axioms graph_then_chart_finite_fibers

end Deligne09
