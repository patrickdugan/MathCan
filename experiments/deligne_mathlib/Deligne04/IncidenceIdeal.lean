import Deligne04.BilinearBadLocus
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Tactic

/-!
# DEL-11: extraction of a principal open from an ideal of bad parameters

For an affine parameter space over a field K, a scheme-theoretic
bad locus can be represented as the common zero locus of an ideal.
If that zero locus omits a geometric point, at least one polynomial
in the ideal does not vanish there. Its principal open is a nonempty
subset of the complement of the bad locus.

This makes explicit the algebraic elimination contract needed to
apply DEL-10's finite-field degree bounds to Bertini and Katz loci:
  (a) construct an ideal whose zero locus covers bad parameters;
  (b) prove its zero locus is proper;
  (c) extract a nonzero polynomial in that ideal with a degree bound.
Only the ideal-to-polynomial implication is proved here. Source
geometry must supply (a), (b), and a quantitative bound for (c).
-/

namespace Deligne11

/-- If one parameter lies outside a polynomial zero locus, a
concrete member of the ideal separates that point from the locus. -/
theorem ideal_separator_of_point_outside
    {K : Type*} [Field K] {σ : Type*}
    (I : Ideal (MvPolynomial σ K)) (point : σ → K)
    (hout : point ∉ MvPolynomial.zeroLocus K I) :
    ∃ P : MvPolynomial σ K,
      P ∈ I ∧ P ≠ 0 ∧ MvPolynomial.eval point P ≠ 0 := by
  classical
  have hx : ¬ (∀ P, P ∈ I → MvPolynomial.aeval point P = 0) := by
    simpa only [MvPolynomial.zeroLocus, Set.mem_setOf_eq] using hout
  push Not at hx
  obtain ⟨P, hP, hval⟩ := hx
  have hv : MvPolynomial.eval point P ≠ 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using hval
  refine ⟨P, hP, ?_, hv⟩
  intro hzero
  apply hv
  simp [hzero]

/-- If all geometrically bad parameters lie in a polynomial ideal's
zero locus and that zero locus omits some point, one nonzero ideal
polynomial cuts out a principal open disjoint from every bad parameter. -/
theorem principal_open_excluding_bad_locus
    {K : Type*} [Field K] {σ : Type*}
    (bad : Set (σ → K)) (I : Ideal (MvPolynomial σ K))
    (hbad : bad ⊆ MvPolynomial.zeroLocus K I)
    (point : σ → K)
    (hpoint : point ∉ MvPolynomial.zeroLocus K I) :
    ∃ P : MvPolynomial σ K,
      P ≠ 0 ∧
      MvPolynomial.eval point P ≠ 0 ∧
      (∀ u, MvPolynomial.eval u P ≠ 0 → u ∉ bad) := by
  obtain ⟨P, hP, hP0, hpointP⟩ :=
    ideal_separator_of_point_outside I point hpoint
  refine ⟨P, hP0, hpointP, ?_⟩
  intro u hnonzero hU
  have hvanish : MvPolynomial.aeval u P = 0 :=
    (hbad hU) P hP
  apply hnonzero
  simpa only [MvPolynomial.aeval_eq_eval] using hvanish

/-- Given one good geometric parameter for both ideal-defined bad
loci, extract a pair of nonzero polynomial certificates. Their
principal opens contain the parameter and exclude the respective
bad loci. -/
theorem two_bad_loci_principal_open_certificates
    {K : Type*} [Field K] {σ : Type*}
    (badB badL : Set (σ → K))
    (IB IL : Ideal (MvPolynomial σ K))
    (hB : badB ⊆ MvPolynomial.zeroLocus K IB)
    (hL : badL ⊆ MvPolynomial.zeroLocus K IL)
    (point : σ → K)
    (hgB : point ∉ MvPolynomial.zeroLocus K IB)
    (hgL : point ∉ MvPolynomial.zeroLocus K IL) :
    ∃ B L : MvPolynomial σ K,
      B ≠ 0 ∧ L ≠ 0 ∧
      MvPolynomial.eval point B ≠ 0 ∧
      MvPolynomial.eval point L ≠ 0 ∧
      (∀ u, MvPolynomial.eval u B ≠ 0 → u ∉ badB) ∧
      (∀ u, MvPolynomial.eval u L ≠ 0 → u ∉ badL) := by
  obtain ⟨B, hB0, hBp, hBgood⟩ :=
    principal_open_excluding_bad_locus badB IB hB point hgB
  obtain ⟨L, hL0, hLp, hLgood⟩ :=
    principal_open_excluding_bad_locus badL IL hL point hgL
  exact ⟨B, L, hB0, hL0, hBp, hLp, hBgood, hLgood⟩

#print axioms ideal_separator_of_point_outside
#print axioms principal_open_excluding_bad_locus
#print axioms two_bad_loci_principal_open_certificates

end Deligne11
