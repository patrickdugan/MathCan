import Deligne04.KahlerSquareZeroBridge
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Tactic

/-!
# DEL-21C: coordinate naturality of the Kähler differential and quotient dual-number tangent

DEL-21A proves that first-order maps from the actual coordinate-ring
quotient A=K[z]/I into DualNumber K correspond to the polynomial
Jacobian tangent. DEL-21B identifies Kähler-linear functionals with
square-zero lifts at a rational point.

This module constructs an explicit scalar readout on the true free
Kähler differential module of the polynomial algebra K[z]. It
extracts coefficients in the genuine Mathlib Kähler basis d(z_i),
evaluates them at u, and pairs against the vector v.

The readout on d(P) is exactly the directional derivative
    sum_i eval_u(pderiv_i P)*v_i,
which is the epsilon coefficient of the DEL-21A dual-number map.
Consequently every quotient-ring dual-number lift from DEL-21A
has epsilon component on the quotient class of P equal to this
Kähler readout of d(P), for *every* polynomial P, and in all
characteristics.

The final quotient Kähler-fiber linear equivalence, including
base change and field extensions, remains a separate DEL-21 target.
-/

open scoped BigOperators

namespace Deligne21C

/-- The actual Kähler-coordinate readout. The polynomial
Kähler module is free with basis d(X_i); repr gives the real
basis coefficients before evaluation at a point. -/
noncomputable def kahlerCoordinateReadout
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K)
    (ω : Ω[MvPolynomial σ K⁄K]) : K :=
  ∑ i : σ,
    MvPolynomial.eval u
      ((KaehlerDifferential.mvPolynomialBasis K σ).repr ω i) * v i

/-- The universal Kähler differential has precisely the true
polynomial partial derivatives as coefficients in its basis. -/
theorem kahler_readout_D_eq_directional
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) (P : MvPolynomial σ K) :
    kahlerCoordinateReadout u v
        (KaehlerDifferential.D K (MvPolynomial σ K) P) =
      Deligne21.tangentDerivative u v P := by
  classical
  simp only [kahlerCoordinateReadout, Deligne21.tangentDerivative,
    KaehlerDifferential.mvPolynomialBasis_repr_apply]

/-- The coefficient of epsilon in the actual dual-number
ring homomorphism equals the Kähler differential readout. -/
theorem firstOrder_snd_eq_kahler_readout
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) (P : MvPolynomial σ K) :
    (Deligne21.firstOrderEvaluation u v P).snd =
      kahlerCoordinateReadout u v
        (KaehlerDifferential.D K (MvPolynomial σ K) P) := by
  rw [kahler_readout_D_eq_directional]
  rfl

/-- Evaluation of the directional derivative of a coordinate
is the prescribed infinitesimal coordinate displacement. -/
theorem tangentDerivative_X
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) (j : σ) :
    Deligne21.tangentDerivative u v
        (MvPolynomial.X j : MvPolynomial σ K) = v j := by
  classical
  unfold Deligne21.tangentDerivative
  calc
    (∑ i : σ,
      MvPolynomial.eval u
        (MvPolynomial.pderiv i (MvPolynomial.X j)) * v i) =
        ∑ i : σ, if i = j then v i else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i = j
          · subst i
            simp
          · have hji : j ≠ i := Ne.symm hij
            simp [hij, MvPolynomial.pderiv_X_of_ne hji]
    _ = v j := by simp

/-- The Kähler readout of d(X_j) is the tangent coordinate v_j. -/
theorem kahler_readout_D_X
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) (j : σ) :
    kahlerCoordinateReadout u v
      (KaehlerDifferential.D K (MvPolynomial σ K)
        (MvPolynomial.X j)) = v j := by
  rw [kahler_readout_D_eq_directional, tangentDerivative_X]

/-- The dual-number image of each coordinate X_j has scalar
component u_j and epsilon component v_j. -/
theorem firstOrder_coordinate
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (u v : σ → K) (j : σ) :
    Deligne21.firstOrderEvaluation u v
        (MvPolynomial.X j) = (u j, v j) := by
  change (MvPolynomial.eval u (MvPolynomial.X j),
      Deligne21.tangentDerivative u v (MvPolynomial.X j)) = (u j, v j)
  simp only [MvPolynomial.eval_X, tangentDerivative_X]

/-- For any actual defining ideal I, a factorization through
K[z]/I agrees on *every polynomial* with its Kähler differential
readout, not just on the generators. This is natural in the
quotient map and retains nilpotent scheme structure. -/
theorem quotient_firstOrder_snd_eq_kahler_readout
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (I : Ideal (MvPolynomial σ K))
    (u v : σ → K)
    (F : (MvPolynomial σ K ⧸ I) →+* DualNumber K)
    (hF : F.comp (Ideal.Quotient.mk I) =
      Deligne21.firstOrderEvaluation u v)
    (P : MvPolynomial σ K) :
    (F ((Ideal.Quotient.mk I) P)).snd =
      kahlerCoordinateReadout u v
        (KaehlerDifferential.D K (MvPolynomial σ K) P) := by
  have hh := congrArg
    (fun h : MvPolynomial σ K →+* DualNumber K => h P) hF
  simp only [RingHom.comp_apply] at hh
  rw [hh]
  exact firstOrder_snd_eq_kahler_readout u v P

/-- The preceding naturality statement at the actual quotient
class of each coordinate X_j. -/
theorem quotient_firstOrder_coordinate
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (I : Ideal (MvPolynomial σ K))
    (u v : σ → K)
    (F : (MvPolynomial σ K ⧸ I) →+* DualNumber K)
    (hF : F.comp (Ideal.Quotient.mk I) =
      Deligne21.firstOrderEvaluation u v)
    (j : σ) :
    F ((Ideal.Quotient.mk I) (MvPolynomial.X j)) =
      (u j, v j) := by
  have hh := congrArg
    (fun h : MvPolynomial σ K →+* DualNumber K =>
      h (MvPolynomial.X j)) hF
  simp only [RingHom.comp_apply] at hh
  rw [hh]
  exact firstOrder_coordinate u v j

/-- Specialization to the actual DEL-16 U^k product ideal and
DEL-20 Jacobian tangent: the quotient first-order lift
simultaneously satisfies the defining ideal and reads out each
coordinate displacement v_i in the Kähler basis. -/
theorem product_tangent_exists_kahler_natural_lift
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u v : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u)
    (hv : v ∈ Deligne20.jacobianTangent f u) :
    ∃ F : (MvPolynomial (Deligne16.Coord k s) K ⧸
        Deligne16.productIdeal f) →+* DualNumber K,
      F.comp (Ideal.Quotient.mk (Deligne16.productIdeal f)) =
        Deligne21.firstOrderEvaluation u v ∧
      ∀ i : Deligne16.Coord k s,
        F ((Ideal.Quotient.mk (Deligne16.productIdeal f))
          (MvPolynomial.X i)) = (u i, v i) := by
  obtain ⟨F, hF⟩ :=
    (Deligne21.product_jacobian_tangent_iff_firstOrder_lift
      f u v hu).mp hv
  refine ⟨F, hF, ?_⟩
  intro i
  exact quotient_firstOrder_coordinate
    (Deligne16.productIdeal f) u v F hF i

#print axioms kahler_readout_D_eq_directional
#print axioms firstOrder_snd_eq_kahler_readout
#print axioms tangentDerivative_X
#print axioms kahler_readout_D_X
#print axioms firstOrder_coordinate
#print axioms quotient_firstOrder_snd_eq_kahler_readout
#print axioms quotient_firstOrder_coordinate
#print axioms product_tangent_exists_kahler_natural_lift

end Deligne21C
