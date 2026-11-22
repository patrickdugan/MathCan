import Deligne04.EffectiveFiniteOpen
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Tactic

/-!
# DEL-11: a concrete bad-hyperplane discriminant and critical incidence

For the smooth ambient affine family
  Σᵢ (xᵢ yᵢ + aᵢ xᵢ + bᵢ yᵢ) + c = 0,
the critical-point parameters are EXACTLY the zeros of
  Δ(a,b,c) = c - Σᵢ aᵢ bᵢ.

The complete-the-square calculation is valid in every characteristic,
including characteristic 2. We construct Δ as a genuine MvPolynomial
in all affine parameter coordinates, prove that it is nonzero, and
show that its nonvanishing principal open excludes every singular
point of the modeled family.

This is a constructive special case of the bad-hyperplane elimination
problem. It does not formalize the general Bertini or Katz opens on U^k.
-/

open scoped BigOperators
open Finset

namespace Deligne11

/-- One affine hypersurface in the bilinear family. -/
def bilinearEquation {K : Type*} [CommRing K] {n : ℕ}
    (a b x y : Fin n → K) (c : K) : K :=
  (∑ i : Fin n, (x i * y i + a i * x i + b i * y i)) + c

/-- Completing the square produces the parameter discriminant. -/
theorem bilinear_complete_square
    {K : Type*} [CommRing K] {n : ℕ}
    (a b x y : Fin n → K) (c : K) :
    bilinearEquation a b x y c =
      (∑ i : Fin n, (x i + b i) * (y i + a i)) +
        c - (∑ i : Fin n, a i * b i) := by
  have hsum :
      (∑ i : Fin n, (x i * y i + a i * x i + b i * y i)) =
        ∑ i : Fin n,
          ((x i + b i) * (y i + a i) - a i * b i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp [bilinearEquation]
  rw [hsum, Finset.sum_sub_distrib]
  ring

/-- Simultaneous vanishing of both gradient blocks and the defining
equation occurs iff the discriminant c - Σ aᵢbᵢ is zero. -/
theorem bilinear_critical_iff
    {K : Type*} [CommRing K] {n : ℕ}
    (a b : Fin n → K) (c : K) :
    (∃ x y : Fin n → K,
      bilinearEquation a b x y c = 0 ∧
      (∀ i, y i + a i = 0) ∧
      (∀ i, x i + b i = 0)) ↔
      c = ∑ i : Fin n, a i * b i := by
  constructor
  · rintro ⟨x, y, hlevel, hdy, hdx⟩
    rw [bilinear_complete_square a b x y c] at hlevel
    have hzero :
        (∑ i : Fin n, (x i + b i) * (y i + a i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hdx i]
      simp
    rw [hzero] at hlevel
    exact sub_eq_zero.mp (by simpa only [zero_add] using hlevel)
  · intro hc
    refine ⟨(fun i => -b i), (fun i => -a i), ?_, ?_, ?_⟩
    · rw [bilinear_complete_square]
      simp [hc]
    · intro i
      ring
    · intro i
      ring

/-- The affine hyperplane parameter coordinates (a,b,c). -/
abbrev ParameterIndex (n : ℕ) := Sum (Sum (Fin n) (Fin n)) Unit

def parameterA {K : Type*} {n : ℕ}
    (u : ParameterIndex n → K) (i : Fin n) : K :=
  u (.inl (.inl i))

def parameterB {K : Type*} {n : ℕ}
    (u : ParameterIndex n → K) (i : Fin n) : K :=
  u (.inl (.inr i))

def parameterC {K : Type*} {n : ℕ}
    (u : ParameterIndex n → K) : K :=
  u (.inr ())

/-- A nonzero defining polynomial for the bad parameter hypersurface. -/
def badDiscriminant (K : Type*) [CommRing K] (n : ℕ) :
    MvPolynomial (ParameterIndex n) K :=
  MvPolynomial.X (.inr ()) -
    ∑ i : Fin n, MvPolynomial.X (.inl (.inl i)) *
      MvPolynomial.X (.inl (.inr i))

theorem eval_badDiscriminant
    {K : Type*} [CommRing K] {n : ℕ}
    (u : ParameterIndex n → K) :
    MvPolynomial.eval u (badDiscriminant K n) =
      parameterC u -
        ∑ i : Fin n, parameterA u i * parameterB u i := by
  simp [badDiscriminant, parameterA, parameterB, parameterC]

/-- The critical-parameter incidence is defined by an existential
quantifier over points of the hypersurface. -/
def criticalParameterSet (K : Type*) [CommRing K] (n : ℕ) :
    Set (ParameterIndex n → K) :=
  {u | ∃ x y : Fin n → K,
      bilinearEquation (parameterA u) (parameterB u) x y
        (parameterC u) = 0 ∧
      (∀ i, y i + parameterA u i = 0) ∧
      (∀ i, x i + parameterB u i = 0)}

/-- The existential incidence eliminates EXACTLY to one equation. -/
theorem critical_iff_badDiscriminant_zero
    {K : Type*} [CommRing K] {n : ℕ}
    (u : ParameterIndex n → K) :
    u ∈ criticalParameterSet K n ↔
      MvPolynomial.eval u (badDiscriminant K n) = 0 := by
  change (∃ x y : Fin n → K,
      bilinearEquation (parameterA u) (parameterB u) x y
        (parameterC u) = 0 ∧
      (∀ i, y i + parameterA u i = 0) ∧
      (∀ i, x i + parameterB u i = 0)) ↔ _
  rw [eval_badDiscriminant, sub_eq_zero]
  exact bilinear_critical_iff (parameterA u) (parameterB u) (parameterC u)

/-- The bad locus is genuinely a polynomial zero set over a field. -/
theorem criticalSet_eq_zeroLocus
    {K : Type*} [Field K] {n : ℕ} :
    criticalParameterSet K n =
      MvPolynomial.zeroLocus K
        (Ideal.span ({badDiscriminant K n} :
          Set (MvPolynomial (ParameterIndex n) K))) := by
  ext u
  rw [MvPolynomial.zeroLocus_span]
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  simpa only [MvPolynomial.coe_aeval_eq_eval] using
    (critical_iff_badDiscriminant_zero u)

/-- A particular point whose c-coordinate is 1 and others are zero. -/
def witnessParameter {K : Type*} [Zero K] [One K] (n : ℕ) :
    ParameterIndex n → K
  | .inr _ => 1
  | .inl _ => 0

/-- The discriminant is a nonzero formal polynomial over any
nontrivial ring, even over the smallest finite field F2. -/
theorem badDiscriminant_ne_zero
    {K : Type*} [CommRing K] [Nontrivial K] (n : ℕ) :
    badDiscriminant K n ≠ 0 := by
  intro hp
  have heval := congrArg
    (MvPolynomial.eval (witnessParameter (K := K) n)) hp
  have hval :
      MvPolynomial.eval (witnessParameter (K := K) n)
        (badDiscriminant K n) = (1 : K) := by
    simp [badDiscriminant, witnessParameter]
  simp [hval] at heval

/-- Nonzero discriminant excludes every singular point, in every
characteristic. This is the algebraic Jacobian certificate. -/
theorem nonzero_discriminant_no_critical_point
    {K : Type*} [CommRing K] {n : ℕ}
    (u : ParameterIndex n → K)
    (h : MvPolynomial.eval u (badDiscriminant K n) ≠ 0) :
    u ∉ criticalParameterSet K n := by
  intro hcrit
  exact h ((critical_iff_badDiscriminant_zero u).mp hcrit)

/-- DEL-10's two-principal-open witness, generalized from Fin n to
any finite index type. This is required because the bilinear parameter
index has a sum type rather than a Fin type. -/
theorem exists_two_good_opens_general
    {K : Type*} [Field K] [Fintype K]
    {σ : Type*} [Finite σ]
    (P Q : MvPolynomial σ K)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hdeg : ∀ i : σ,
      P.degreeOf i + Q.degreeOf i < Fintype.card K) :
    ∃ x : σ → K,
      MvPolynomial.eval x P ≠ 0 ∧
      MvPolynomial.eval x Q ≠ 0 := by
  classical
  have hPQ : P * Q ≠ 0 := mul_ne_zero hP hQ
  have hdegree : ∀ i : σ,
      (P * Q).degreeOf i < Fintype.card K := by
    intro i
    exact (MvPolynomial.degreeOf_mul_le i P Q).trans_lt (hdeg i)
  have hsome : ∃ x : σ → K,
      MvPolynomial.eval x (P * Q) ≠ 0 := by
    by_contra h
    apply hPQ
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset
      (P * Q) (fun _ : σ => Finset.univ)
    · intro i
      simpa using hdegree i
    · intro x _
      by_contra hx
      exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hsome
  have hmul :
      MvPolynomial.eval x P * MvPolynomial.eval x Q ≠ 0 := by
    simpa only [map_mul] using hx
  constructor
  · intro hp
    exact hmul (by rw [hp, zero_mul])
  · intro hq
    exact hmul (by rw [hq, mul_zero])

#print axioms exists_two_good_opens_general

/-- If another nonzero polynomial cuts out the Katz good locus,
DEL-10's effective theorem selects a single rational point outside
the exact singular locus and inside that Katz principal open.
The degree budget is an explicit input from the geometry. -/
theorem exists_regular_and_katz_good_parameter
    {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (L : MvPolynomial (ParameterIndex n) K)
    (hL : L ≠ 0)
    (hbudget : ∀ i : ParameterIndex n,
      (badDiscriminant K n).degreeOf i + L.degreeOf i <
        Fintype.card K) :
    ∃ u : ParameterIndex n → K,
      u ∉ criticalParameterSet K n ∧
      MvPolynomial.eval u L ≠ 0 := by
  obtain ⟨u, hP, hLval⟩ :=
    exists_two_good_opens_general
      (badDiscriminant K n) L
      (badDiscriminant_ne_zero n) hL hbudget
  exact ⟨u, nonzero_discriminant_no_critical_point u hP, hLval⟩

#print axioms bilinear_complete_square
#print axioms bilinear_critical_iff
#print axioms eval_badDiscriminant
#print axioms critical_iff_badDiscriminant_zero
#print axioms criticalSet_eq_zeroLocus
#print axioms badDiscriminant_ne_zero
#print axioms nonzero_discriminant_no_critical_point
#print axioms exists_regular_and_katz_good_parameter

end Deligne11
