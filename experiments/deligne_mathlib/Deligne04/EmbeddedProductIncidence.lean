import Deligne04.EmbeddedLineBadLocus
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic

/-!
# DEL-16: embedded-product equations and relative tangent incidence

An arbitrary affine closed-embedding presentation of U is given by
f₀,...,f_{r-1} in K[z₀,...,z_{s-1}]. We lift these actual
polynomials into the ambient coordinate ring of U^k by renaming
their variables into the chosen product factor.

The prescribed last embedding coordinate is a fixed polynomial B
in the ambient variables of U^k (in the application: the path
bilinear form). The hyperplane-section polynomial is
  B + ∑ a_j X_j + c.
Its last-coordinate coefficient is identically one.

A relative critical-point certificate uses actual formal partial
derivatives and multipliers for the equations of U^k. We prove
that such a certificate annihilates every tangent vector to the
presented product. For a smooth complete intersection whose
constraint Jacobian has full rank, the usual Jacobian criterion
makes this certificate necessary as well as sufficient.

The general elimination lemma proves every point of an incidence
ideal's zero locus yields a parameter annihilating the pulled-back
elimination ideal. Properness and degree estimates still need the
Bertini geometry; Katz weak Lefschetz remains separate.
-/

open scoped BigOperators
open Finset

namespace Deligne16

abbrev Coord (k s : ℕ) := Fin k × Fin s
abbrev EqCoord (k r : ℕ) := Fin k × Fin r

/-- Embed one polynomial defining U into the appropriate factor
of the genuine ambient polynomial ring for U^k. -/
noncomputable def copyEquation
    {K : Type*} [CommRing K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (t : EqCoord k r) :
    MvPolynomial (Coord k s) K :=
  MvPolynomial.rename (fun i : Fin s => (t.1, i)) (f t.2)

/-- The lifted equation evaluates exactly on its chosen factor. -/
theorem eval_copyEquation
    {K : Type*} [CommRing K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Coord k s → K) (t : EqCoord k r) :
    MvPolynomial.eval u (copyEquation f t) =
      MvPolynomial.eval (fun i : Fin s => u (t.1, i)) (f t.2) := by
  simpa [copyEquation] using
    (MvPolynomial.eval_rename_prod_mk u t.1 (f t.2))

/-- The actual equations of the k-fold embedded product. -/
def onEmbeddedProduct
    {K : Type*} [CommRing K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Coord k s → K) : Prop :=
  ∀ t : EqCoord k r, MvPolynomial.eval u (copyEquation f t) = 0

/-- The Cartesian-product vanishing test is equivalent to
membership of every factor in the original affine zero locus. -/
theorem onEmbeddedProduct_iff
    {K : Type*} [CommRing K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Coord k s → K) :
    onEmbeddedProduct f u ↔
      ∀ j : Fin k, ∀ h : Fin r,
        MvPolynomial.eval (fun i : Fin s => u (j,i)) (f h) = 0 := by
  constructor
  · intro h j q
    simpa only [eval_copyEquation] using h (j, q)
  · intro h ⟨j, q⟩
    simpa only [eval_copyEquation] using h j q

/-- The defining ideal in K[coordinates of U^k]. -/
noncomputable def productIdeal
    {K : Type*} [CommRing K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K) :
    Ideal (MvPolynomial (Coord k s) K) :=
  Ideal.span (Set.range (copyEquation f))

/-- Pull back a hyperplane with fixed coefficient 1 on B.
For the intended application B is the explicit bilinear path
coordinate from DEL-08. -/
noncomputable def fixedSection
    {K : Type*} [CommRing K] {k s : ℕ}
    (B : MvPolynomial (Coord k s) K)
    (a : Coord k s → K) (c : K) :
    MvPolynomial (Coord k s) K :=
  B + (∑ i : Coord k s,
    MvPolynomial.C (a i) * MvPolynomial.X i) + MvPolynomial.C c

theorem eval_fixedSection
    {K : Type*} [CommRing K] {k s : ℕ}
    (B : MvPolynomial (Coord k s) K)
    (a : Coord k s → K) (c : K)
    (u : Coord k s → K) :
    MvPolynomial.eval u (fixedSection B a c) =
      MvPolynomial.eval u B +
        (∑ i : Coord k s, a i * u i) + c := by
  simp [fixedSection]

/-- Tangency uses the true Mathlib polynomial derivations for
every embedded-product defining equation. -/
def isProductTangent
    {K : Type*} [CommRing K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u v : Coord k s → K) : Prop :=
  ∀ t : EqCoord k r,
    (∑ i : Coord k s,
       MvPolynomial.eval u
         (MvPolynomial.pderiv i (copyEquation f t)) * v i) = 0

/-- A relative critical-point certificate in the smooth
complete-intersection case: the hyperplane-section derivative
lies in the row span of the constraint Jacobian, and the point
lies on the section. -/
def isLagrangeCritical
    {K : Type*} [CommRing K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Coord k s) K)
    (a : Coord k s → K) (c : K)
    (u : Coord k s → K) : Prop :=
  onEmbeddedProduct f u ∧
    MvPolynomial.eval u (fixedSection B a c) = 0 ∧
    ∃ lam : EqCoord k r → K,
      ∀ i : Coord k s,
        MvPolynomial.eval u
          (MvPolynomial.pderiv i (fixedSection B a c)) =
          ∑ t : EqCoord k r, lam t *
            MvPolynomial.eval u
              (MvPolynomial.pderiv i (copyEquation f t))

/-- Elementary finite-dimensional normal/tangent pairing. -/
theorem weighted_jacobian_tangent_zero
    {K : Type*} [CommRing K]
    {α β : Type*} [Fintype α] [Fintype β]
    (J : β → α → K) (g v : α → K) (lam : β → K)
    (hgradient : ∀ i, g i = ∑ t : β, lam t * J t i)
    (htangent : ∀ t, ∑ i : α, J t i * v i = 0) :
    (∑ i : α, g i * v i) = 0 := by
  classical
  calc
    (∑ i : α, g i * v i) =
        ∑ i : α, (∑ t : β, lam t * J t i) * v i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hgradient i]
    _ = ∑ t : β, ∑ i : α, lam t * (J t i * v i) := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          simp_rw [mul_assoc]
    _ = ∑ t : β, lam t * (∑ i : α, J t i * v i) := by
          simp_rw [Finset.mul_sum]
    _ = 0 := by simp [htangent]

/-- Every algebraically certified relative critical point has
zero directional derivative on every tangent vector of U^k.
This retains the true polynomial derivatives and works in
characteristic two. -/
theorem lagrange_critical_annihilates_product_tangent
    {K : Type*} [CommRing K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Coord k s) K)
    (a : Coord k s → K) (c : K)
    (u v : Coord k s → K)
    (hcrit : isLagrangeCritical f B a c u)
    (htangent : isProductTangent f u v) :
    (∑ i : Coord k s,
       MvPolynomial.eval u
         (MvPolynomial.pderiv i (fixedSection B a c)) * v i) = 0 := by
  obtain ⟨_, _, lam, hlam⟩ := hcrit
  exact weighted_jacobian_tangent_zero
    (fun t i => MvPolynomial.eval u
      (MvPolynomial.pderiv i (copyEquation f t)))
    (fun i => MvPolynomial.eval u
      (MvPolynomial.pderiv i (fixedSection B a c)))
    v lam hlam htangent

/-- Project a joint incidence ideal in K[parameters, witness]
back to the genuine parameter polynomial ring using a ring-hom
ideal comap, the algebraic elimination ideal. -/
noncomputable def eliminationIdeal
    {K : Type*} [CommRing K] {σ τ : Type*}
    (I : Ideal (MvPolynomial (Sum σ τ) K)) :
    Ideal (MvPolynomial σ K) :=
  Ideal.comap
    (MvPolynomial.rename (Sum.inl : σ → Sum σ τ)) I

/-- A point of the joint incidence variety vanishes on every
eliminated polynomial at its projected parameter. This is the
soundness direction of algebraic elimination over every field;
proving the eliminated ideal has a nonzero member is geometric. -/
theorem elimination_sound_at_joint_zero
    {K : Type*} [Field K] {σ τ : Type*}
    (I : Ideal (MvPolynomial (Sum σ τ) K))
    (u : Sum σ τ → K)
    (hzero : ∀ Q : MvPolynomial (Sum σ τ) K,
      Q ∈ I → MvPolynomial.eval u Q = 0)
    (P : MvPolynomial σ K)
    (hP : P ∈ eliminationIdeal I) :
    MvPolynomial.eval (fun i : σ => u (.inl i)) P = 0 := by
  have hm : MvPolynomial.rename (Sum.inl : σ → Sum σ τ) P ∈ I := hP
  have hv := hzero _ hm
  have heq : (u ∘ (Sum.inl : σ → Sum σ τ)) =
      (fun i : σ => u (.inl i)) := by
    funext i
    rfl
  simpa only [MvPolynomial.eval_rename, heq] using hv

#print axioms eval_copyEquation
#print axioms onEmbeddedProduct_iff
#print axioms eval_fixedSection
#print axioms weighted_jacobian_tangent_zero
#print axioms lagrange_critical_annihilates_product_tangent
#print axioms elimination_sound_at_joint_zero

end Deligne16
