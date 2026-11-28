import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-!
# DEL-10: effective nonvanishing witnesses for finite-field open loci

The missing parameter-selection step in the geometric proof can be
made effective whenever the desired good hyperplanes contain a
principal open D(P) and the finite field is large enough relative
to the degree of P in each coordinate.

The theorem is an actual Mathlib consequence of the multivariate
polynomial vanishing lemma (combinatorial Nullstellensatz).
It proves a finite-field RATIONAL POINT rather than assuming that
nonempty geometric opens already have points over the base field.

The geometric step identifying the Bertini and Katz good loci with
specific principal polynomial opens remains an external hypothesis.
-/

open scoped BigOperators
open Finset

namespace Deligne10

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

/-- A nonzero multivariate polynomial over a finite field has a
nonvanishing rational evaluation if its degree in each variable is
strictly smaller than the cardinality of the field. -/
theorem exists_nonzero_eval_of_degree_lt_card
    (P : MvPolynomial (Fin n) F)
    (hP : P ≠ 0)
    (hdeg : ∀ i : Fin n, P.degreeOf i < Fintype.card F) :
    ∃ x : Fin n → F, MvPolynomial.eval x P ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hP
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset
    P (fun _ : Fin n => Finset.univ)
  · intro i
    simpa using hdeg i
  · intro x _
    exact h x

/-- If two desired good loci are principal opens D(P), D(Q),
then the intersection has a rational point whenever the sum of
their degree budgets remains below the field size. -/
theorem exists_point_in_two_good_opens
    (P Q : MvPolynomial (Fin n) F)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hdeg : ∀ i : Fin n,
      P.degreeOf i + Q.degreeOf i < Fintype.card F) :
    ∃ x : Fin n → F,
      MvPolynomial.eval x P ≠ 0 ∧
      MvPolynomial.eval x Q ≠ 0 := by
  have hPQ : P * Q ≠ 0 := mul_ne_zero hP hQ
  have hdegreePQ : ∀ i : Fin n,
      (P * Q).degreeOf i < Fintype.card F := by
    intro i
    exact (MvPolynomial.degreeOf_mul_le i P Q).trans_lt (hdeg i)
  obtain ⟨x, hx⟩ :=
    exists_nonzero_eval_of_degree_lt_card (P * Q) hPQ hdegreePQ
  have hmul : (MvPolynomial.eval x P) * (MvPolynomial.eval x Q) ≠ 0 := by
    simpa only [map_mul] using hx
  have hp : MvPolynomial.eval x P ≠ 0 := by
    intro hp
    apply hmul
    rw [hp, zero_mul]
  have hq : MvPolynomial.eval x Q ≠ 0 := by
    intro hq
    apply hmul
    rw [hq, mul_zero]
  exact ⟨x, hp, hq⟩

/-- Three constraints: a Bertini smoothness polynomial, a Katz
weak-Lefschetz polynomial, and a principal chart polynomial can all
be nonzero at the same finite-field point when the coordinate-wise
degree budget fits below the field cardinality. -/
theorem exists_bertini_lefschetz_chart_point
    (B L C : MvPolynomial (Fin n) F)
    (hB : B ≠ 0) (hL : L ≠ 0) (hC : C ≠ 0)
    (hdeg : ∀ i : Fin n,
      B.degreeOf i + L.degreeOf i + C.degreeOf i <
        Fintype.card F) :
    ∃ x : Fin n → F,
      MvPolynomial.eval x B ≠ 0 ∧
      MvPolynomial.eval x L ≠ 0 ∧
      MvPolynomial.eval x C ≠ 0 := by
  have hBL : B * L ≠ 0 := mul_ne_zero hB hL
  have hdegBLC : ∀ i : Fin n,
      (B * L).degreeOf i + C.degreeOf i <
        Fintype.card F := by
    intro i
    have hmul := MvPolynomial.degreeOf_mul_le i B L
    have htotal := hdeg i
    omega
  obtain ⟨x, hBLval, hCval⟩ :=
    exists_point_in_two_good_opens (B * L) C hBL hC hdegBLC
  have hmul : (MvPolynomial.eval x B) *
      (MvPolynomial.eval x L) ≠ 0 := by
    simpa only [map_mul] using hBLval
  have hBval : MvPolynomial.eval x B ≠ 0 := by
    intro hb
    apply hmul
    rw [hb, zero_mul]
  have hLval : MvPolynomial.eval x L ≠ 0 := by
    intro hl
    apply hmul
    rw [hl, mul_zero]
  exact ⟨x, hBval, hLval, hCval⟩

#print axioms exists_nonzero_eval_of_degree_lt_card
#print axioms exists_point_in_two_good_opens
#print axioms exists_bertini_lefschetz_chart_point

end Deligne10
