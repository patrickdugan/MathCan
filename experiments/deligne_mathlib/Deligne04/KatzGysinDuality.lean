import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

/-!
# DEL-07: Poincare-dual Gysin maps from ordinary restriction maps

This is a coordinate-free linear-algebraic interface for the
restriction/Gysin transposition in Hexagon 2611.00789v1,
Proposition 4 and Katz, Appendix A.5. A true Poincare pairing is
represented by a supplied linear equivalence with the algebraic
dual. Geometric existence and perfectness of these pairings are
explicit external premises.

The ordinary actions used below are inverse Frobenius, with an optional
common Tate factor made explicit in the normalized theorem. Poincare
duality is contragredient, so forward Frobenius alone would misstate
this square.
-/

namespace Deligne07

universe u v w z

variable {HX : Type u} {HY : Type v} {CX : Type w} {CY : Type z}
variable [AddCommGroup HX] [Module ℂ HX]
variable [AddCommGroup HY] [Module ℂ HY]
variable [AddCommGroup CX] [Module ℂ CX]
variable [AddCommGroup CY] [Module ℂ CY]

/-- A single cohomological degree of a Poincare-duality diagram.

HX and HY are the ordinary cohomology groups in the same degree.
CX and CY are the appropriately shifted and Tate-twisted compact
cohomology groups. The pairings are perfect, and their Frobenius
compatibility is supplied separately, not inferred from vector spaces.
-/
structure PerfectPairingGysin (HX HY CX CY : Type*)
    [AddCommGroup HX] [Module ℂ HX]
    [AddCommGroup HY] [Module ℂ HY]
    [AddCommGroup CX] [Module ℂ CX]
    [AddCommGroup CY] [Module ℂ CY] where
  restriction : HX →ₗ[ℂ] HY
  pdX : CX ≃ₗ[ℂ] Module.Dual ℂ HX
  pdY : CY ≃ₗ[ℂ] Module.Dual ℂ HY

namespace PerfectPairingGysin

variable (P : PerfectPairingGysin HX HY CX CY)

/-- The genuine transpose of ordinary cohomological restriction,
transported by perfect pairings. -/
def gysin : CY →ₗ[ℂ] CX :=
  P.pdX.symm.toLinearMap.comp
    (P.restriction.dualMap.comp P.pdY.toLinearMap)

/-- Katz's boundary injectivity forces Gysin surjectivity.
The only non-geometric input is the linear-algebra theorem that
the dual of an injective vector-space map is surjective. -/
theorem gysin_surjective_of_restriction_injective
    (h : Function.Injective P.restriction) :
    Function.Surjective P.gysin := by
  intro x
  obtain ⟨psi, hpsi⟩ :=
    (LinearMap.dualMap_surjective_of_injective h) (P.pdX x)
  refine ⟨P.pdY.symm psi, ?_⟩
  simp [gysin, hpsi]

/-- When restriction is surjective, its dual Gysin is injective. -/
theorem gysin_injective_of_restriction_surjective
    (h : Function.Surjective P.restriction) :
    Function.Injective P.gysin := by
  intro y y' hEq
  change P.pdX.symm (P.restriction.dualMap (P.pdY y)) =
      P.pdX.symm (P.restriction.dualMap (P.pdY y')) at hEq
  apply P.pdY.injective
  apply LinearMap.dualMap_injective_of_surjective h
  exact P.pdX.symm.injective hEq

/-- Katz's strict-degree isomorphism transfers to a genuine Gysin
isomorphism, with no requirement that restriction preserve a chosen
basis. -/
theorem gysin_bijective_of_restriction_bijective
    (h : Function.Bijective P.restriction) :
    Function.Bijective P.gysin :=
  ⟨P.gysin_injective_of_restriction_surjective h.2,
   P.gysin_surjective_of_restriction_injective h.1⟩

/-- A square expressing the inverse Frobenius action on ordinary
cohomology, and the dual Frobenius action on compact cohomology,
makes the transposed Gysin map equivariant. -/
theorem gysin_frobenius_equivariant
    (FXinv : HX →ₗ[ℂ] HX) (FYinv : HY →ₗ[ℂ] HY)
    (FCX : CX →ₗ[ℂ] CX) (FCY : CY →ₗ[ℂ] CY)
    (hres : FYinv.comp P.restriction =
      P.restriction.comp FXinv)
    (hpdX : ∀ x, P.pdX (FCX x) =
      FXinv.dualMap (P.pdX x))
    (hpdY : ∀ y, P.pdY (FCY y) =
      FYinv.dualMap (P.pdY y)) :
    P.gysin.comp FCY = FCX.comp P.gysin := by
  have hdual :
      P.restriction.dualMap.comp FYinv.dualMap =
        FXinv.dualMap.comp P.restriction.dualMap := by
    rw [LinearMap.dualMap_comp_dualMap P.restriction FYinv,
        LinearMap.dualMap_comp_dualMap FXinv P.restriction]
    exact congrArg LinearMap.dualMap hres
  apply LinearMap.ext
  intro y
  apply P.pdX.injective
  have hg (t : CY) :
      P.pdX (P.gysin t) =
        P.restriction.dualMap (P.pdY t) := by
    simp [gysin]
  calc
    P.pdX (P.gysin (FCY y)) =
        P.restriction.dualMap (P.pdY (FCY y)) := hg _
    _ = P.restriction.dualMap (FYinv.dualMap (P.pdY y)) := by
      rw [hpdY y]
    _ = FXinv.dualMap (P.restriction.dualMap (P.pdY y)) := by
      exact LinearMap.congr_fun hdual (P.pdY y)
    _ = FXinv.dualMap (P.pdX (P.gysin y)) := by rw [hg y]
    _ = P.pdX (FCX (P.gysin y)) := (hpdX _).symm

/-- The precise Tate-normalized Frobenius statement. Poincare
duality transports compact Frobenius to the dual of inverse ordinary
Frobenius times one common scalar t. In codimension one, the
(-1) twist makes this scalar equal to r^D on both sides, so the
restriction square still dualizes equivariantly. -/
theorem gysin_frobenius_equivariant_tate
    (FXinv : HX →ₗ[ℂ] HX) (FYinv : HY →ₗ[ℂ] HY)
    (FCX : CX →ₗ[ℂ] CX) (FCY : CY →ₗ[ℂ] CY)
    (t : ℂ)
    (hres : FYinv.comp P.restriction =
      P.restriction.comp FXinv)
    (hpdX : ∀ x, P.pdX (FCX x) =
      t • FXinv.dualMap (P.pdX x))
    (hpdY : ∀ y, P.pdY (FCY y) =
      t • FYinv.dualMap (P.pdY y)) :
    P.gysin.comp FCY = FCX.comp P.gysin := by
  have hdual :
      P.restriction.dualMap.comp FYinv.dualMap =
        FXinv.dualMap.comp P.restriction.dualMap := by
    rw [LinearMap.dualMap_comp_dualMap P.restriction FYinv,
        LinearMap.dualMap_comp_dualMap FXinv P.restriction]
    exact congrArg LinearMap.dualMap hres
  apply LinearMap.ext
  intro y
  apply P.pdX.injective
  have hg (u : CY) :
      P.pdX (P.gysin u) =
        P.restriction.dualMap (P.pdY u) := by
    simp [gysin]
  calc
    P.pdX (P.gysin (FCY y)) =
        P.restriction.dualMap (P.pdY (FCY y)) := hg _
    _ = P.restriction.dualMap
        (t • FYinv.dualMap (P.pdY y)) := by
          rw [hpdY y]
    _ = t • P.restriction.dualMap
        (FYinv.dualMap (P.pdY y)) := by
          rw [map_smul]
    _ = t • FXinv.dualMap
        (P.restriction.dualMap (P.pdY y)) := by
          have hfun := LinearMap.congr_fun hdual (P.pdY y)
          simpa only [LinearMap.comp_apply] using
            congrArg (fun v : Module.Dual ℂ HX => t • v) hfun
    _ = t • FXinv.dualMap (P.pdX (P.gysin y)) := by
          rw [hg y]
    _ = P.pdX (FCX (P.gysin y)) := (hpdX _).symm

#print axioms gysin_frobenius_equivariant_tate

/-- The kernel of an equivariant Gysin map is Frobenius-stable. -/
theorem gysin_kernel_stable
    (FCX : CX →ₗ[ℂ] CX) (FCY : CY →ₗ[ℂ] CY)
    (hequiv : P.gysin.comp FCY = FCX.comp P.gysin)
    (y : CY) (hy : y ∈ LinearMap.ker P.gysin) :
    FCY y ∈ LinearMap.ker P.gysin := by
  have hy0 : P.gysin y = 0 := LinearMap.mem_ker.mp hy
  have h := congrArg
    (fun f : CY →ₗ[ℂ] CX => f y) hequiv
  change P.gysin (FCY y) = FCX (P.gysin y) at h
  rw [hy0, map_zero] at h
  exact LinearMap.mem_ker.mpr h

/-- The single boundary Gysin kernel from Katz's injectivity is
an actual stable submodule, assuming the Frobenius-equivariance
supplied by the perfect pairings. -/
theorem boundary_kernel_from_katz_injection
    (FXinv : HX →ₗ[ℂ] HX) (FYinv : HY →ₗ[ℂ] HY)
    (FCX : CX →ₗ[ℂ] CX) (FCY : CY →ₗ[ℂ] CY)
    (hinj : Function.Injective P.restriction)
    (hres : FYinv.comp P.restriction =
      P.restriction.comp FXinv)
    (hpdX : ∀ x, P.pdX (FCX x) =
      FXinv.dualMap (P.pdX x))
    (hpdY : ∀ y, P.pdY (FCY y) =
      FYinv.dualMap (P.pdY y)) :
    Function.Surjective P.gysin ∧
      (∀ y ∈ LinearMap.ker P.gysin,
        FCY y ∈ LinearMap.ker P.gysin) := by
  constructor
  · exact P.gysin_surjective_of_restriction_injective hinj
  · intro y hy
    exact P.gysin_kernel_stable FCX FCY
      (P.gysin_frobenius_equivariant
        FXinv FYinv FCX FCY hres hpdX hpdY) y hy

/-- The first isomorphism theorem turns a surjective boundary
Gysin map into a genuine quotient-by-kernel equivalence. -/
noncomputable def boundaryQuotientEquiv
    (hinj : Function.Injective P.restriction) :
    (CY ⧸ LinearMap.ker P.gysin) ≃ₗ[ℂ] CX :=
  P.gysin.quotKerEquivOfSurjective
    (P.gysin_surjective_of_restriction_injective hinj)

/-- Frobenius descends to the quotient by an invariant Gysin kernel. -/
def boundaryQuotientFrobenius
    (FCX : CX →ₗ[ℂ] CX) (FCY : CY →ₗ[ℂ] CY)
    (hequiv : P.gysin.comp FCY = FCX.comp P.gysin) :
    (CY ⧸ LinearMap.ker P.gysin) →ₗ[ℂ]
      (CY ⧸ LinearMap.ker P.gysin) :=
  Submodule.mapQ (LinearMap.ker P.gysin)
    (LinearMap.ker P.gysin) FCY (by
      intro y hy
      exact P.gysin_kernel_stable FCX FCY hequiv y hy)

/-- Under the exact-sequence isomorphism, the induced quotient
Frobenius agrees with the target compact-cohomology Frobenius.
This identifies the quotient as an actual Frobenius module. -/
theorem boundaryQuotientFrobenius_intertwines
    (hinj : Function.Injective P.restriction)
    (FCX : CX →ₗ[ℂ] CX) (FCY : CY →ₗ[ℂ] CY)
    (hequiv : P.gysin.comp FCY = FCX.comp P.gysin) :
    (P.boundaryQuotientEquiv hinj).toLinearMap.comp
        (P.boundaryQuotientFrobenius FCX FCY hequiv) =
      FCX.comp (P.boundaryQuotientEquiv hinj).toLinearMap := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro y
  have h := congrArg
    (fun f : CY →ₗ[ℂ] CX => f y) hequiv
  change P.gysin (FCY y) = FCX (P.gysin y) at h
  simpa [boundaryQuotientEquiv, boundaryQuotientFrobenius,
    LinearMap.comp_apply] using h

#print axioms boundaryQuotientFrobenius_intertwines

#print axioms gysin_surjective_of_restriction_injective
#print axioms gysin_injective_of_restriction_surjective
#print axioms gysin_bijective_of_restriction_bijective
#print axioms gysin_frobenius_equivariant
#print axioms gysin_kernel_stable
#print axioms boundary_kernel_from_katz_injection

end PerfectPairingGysin

end Deligne07
