module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-!
# Finite averaging of an additive two-cocycle

The coefficient is the negative of an actual finite row sum. Summing a
two-cocycle identity and reindexing by a group translation proves its addition
law. No cardinal is inverted, so the construction includes characteristics
dividing the group order. Identifying the geometric slope with a two-cocycle
is a separate input supplied by the curve application.
-/

namespace TRR08Geometry.FiniteSlopeAverage

open scoped BigOperators

section Additive

variable {G A : Type*} [AddGroup G] [Fintype G] [AddCommGroup A]

/-- The finite row sum of the given function. -/
def rowSum (c : G → G → A) (P : G) : A := ∑ R : G, c P R

/-- The coefficient associated with a row of the finite cocycle. -/
def coefficient (c : G → G → A) (P : G) : A := -rowSum c P

/-- Reindexing uses the actual bijection given by a group translation. -/
theorem translate_row_sum (c : G → G → A) (P Q : G) :
    (∑ R : G, c P (Q + R)) = rowSum c P := by
  exact Fintype.sum_equiv (Equiv.addLeft Q) (fun R => c P (Q + R)) (c P) (fun _ => rfl)

/-- Sum the fixed-pair identity over its remaining argument. -/
theorem rowSum_add_of_identity (c : G → G → A) (P Q : G)
    (hc : ∀ R, c P Q + c (P + Q) R = c Q R + c P (Q + R)) :
    Fintype.card G • c P Q + rowSum c (P + Q) = rowSum c Q + rowSum c P := by
  have hs : (∑ R : G, (c P Q + c (P + Q) R)) =
      ∑ R : G, (c Q R + c P (Q + R)) := by
    exact Finset.sum_congr rfl (fun R _ => hc R)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, translate_row_sum c P Q] at hs
  exact hs

theorem rowSum_add (c : G → G → A)
    (hc : ∀ P Q R, c P Q + c (P + Q) R = c Q R + c P (Q + R))
    (P Q : G) :
    Fintype.card G • c P Q + rowSum c (P + Q) = rowSum c Q + rowSum c P :=
  rowSum_add_of_identity c P Q (hc P Q)

/-- The negative row sum gives an integral coboundary identity for a fixed pair. -/
theorem coefficient_add_nsmul_of_identity (c : G → G → A) (P Q : G)
    (hc : ∀ R, c P Q + c (P + Q) R = c Q R + c P (Q + R)) :
    coefficient c (P + Q) = coefficient c P + coefficient c Q +
      Fintype.card G • c P Q := by
  have hs := rowSum_add_of_identity c P Q hc
  have hr : rowSum c (P + Q) = rowSum c Q + rowSum c P - Fintype.card G • c P Q := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hs
  unfold coefficient
  rw [hr]
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
  ac_rfl

theorem coefficient_add_nsmul (c : G → G → A)
    (hc : ∀ P Q R, c P Q + c (P + Q) R = c Q R + c P (Q + R))
    (P Q : G) :
    coefficient c (P + Q) = coefficient c P + coefficient c Q +
      Fintype.card G • c P Q :=
  coefficient_add_nsmul_of_identity c P Q (hc P Q)

theorem coefficient_zero (c : G → G → A) (hz : ∀ R, c 0 R = 0) :
    coefficient c 0 = 0 := by
  simp [coefficient, rowSum, hz]

end Additive

section Ring

variable {G K : Type*} [AddGroup G] [Fintype G] [Ring K]

/-- Ring-valued form, with the group cardinal cast into the ring. -/
theorem coefficient_add (c : G → G → K)
    (hc : ∀ P Q R, c P Q + c (P + Q) R = c Q R + c P (Q + R))
    (P Q : G) :
    coefficient c (P + Q) = coefficient c P + coefficient c Q +
      (Fintype.card G : K) * c P Q := by
  simpa only [nsmul_eq_mul] using coefficient_add_nsmul c hc P Q

theorem coefficient_double (c : G → G → K)
    (hc : ∀ P Q R, c P Q + c (P + Q) R = c Q R + c P (Q + R))
    (P : G) :
    coefficient c (P + P) = 2 * coefficient c P +
      (Fintype.card G : K) * c P P := by
  simpa only [two_mul] using coefficient_add c hc P P

/-- Doubling needs only the diagonal identity at the one chosen point. -/
theorem coefficient_double_of_diagonal (c : G → G → K) (P : G)
    (hc : ∀ R, c P P + c (P + P) R = c P R + c P (P + R)) :
    coefficient c (P + P) = 2 * coefficient c P +
      (Fintype.card G : K) * c P P := by
  simpa only [nsmul_eq_mul, two_mul] using coefficient_add_nsmul_of_identity c P P hc

/-- Restrict the coefficient to the sequence of multiples of a marked point. -/
def coefficientSequence (c : G → G → K) (T : G) (k : ℕ) : K :=
  coefficient c (k • T)

theorem coefficientSequence_add (c : G → G → K)
    (hc : ∀ P Q R, c P Q + c (P + Q) R = c Q R + c P (Q + R))
    (T : G) (i j : ℕ) :
    coefficientSequence c T (i + j) = coefficientSequence c T i +
      coefficientSequence c T j + (Fintype.card G : K) * c (i • T) (j • T) := by
  simpa only [coefficientSequence, add_nsmul] using coefficient_add c hc (i • T) (j • T)

theorem coefficientSequence_double (c : G → G → K)
    (hc : ∀ P Q R, c P Q + c (P + Q) R = c Q R + c P (Q + R))
    (T : G) (k : ℕ) :
    coefficientSequence c T (2 * k) = 2 * coefficientSequence c T k +
      (Fintype.card G : K) * c (k • T) (k • T) := by
  simpa only [two_mul] using coefficientSequence_add c hc T k k

end Ring

section Cyclic

variable {G K : Type*} [AddGroup G] [Ring K]

/-- The finite enumeration of the actual cyclic subgroup supplied by its order. -/
@[instance_reducible] noncomputable def cyclicFintype (T : G) (hT : IsOfFinAddOrder T) :
    Fintype (AddSubgroup.zmultiples T) :=
  Fintype.ofEquiv (Fin (addOrderOf T)) (finEquivZMultiples hT)

theorem cyclic_card (T : G) (hT : IsOfFinAddOrder T)
    [Fintype (AddSubgroup.zmultiples T)] :
    Fintype.card (AddSubgroup.zmultiples T) = addOrderOf T := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (finEquivZMultiples hT)).symm

/-- Sum over the actual cyclic subgroup, even when the ambient group is infinite. -/
noncomputable def cyclicCoefficient (c : G → G → K) (T : G)
    (hT : IsOfFinAddOrder T) (k : ℕ) : K :=
  letI := cyclicFintype T hT;
  -(∑ R : AddSubgroup.zmultiples T, c (k • T) R)

theorem cyclicCoefficient_add (c : G → G → K)
    (hc : ∀ P Q R, c P Q + c (P + Q) R = c Q R + c P (Q + R))
    (T : G) (hT : IsOfFinAddOrder T) (i j : ℕ) :
    cyclicCoefficient c T hT (i + j) = cyclicCoefficient c T hT i +
      cyclicCoefficient c T hT j + (addOrderOf T : K) * c (i • T) (j • T) := by
  classical
  let := cyclicFintype T hT
  let c' : AddSubgroup.zmultiples T → AddSubgroup.zmultiples T → K :=
    fun P Q => c P Q
  have hc' : ∀ P Q R, c' P Q + c' (P + Q) R = c' Q R + c' P (Q + R) := by
    intro P Q R
    exact hc P Q R
  let Pi : AddSubgroup.zmultiples T := ⟨i • T, ⟨(i : ℤ), by simp⟩⟩
  let Pj : AddSubgroup.zmultiples T := ⟨j • T, ⟨(j : ℤ), by simp⟩⟩
  have hs := coefficient_add c' hc' Pi Pj
  simpa only [coefficient, rowSum, cyclicCoefficient, c', Pi, Pj,
    AddSubgroup.coe_add, add_nsmul, cyclic_card T hT] using hs

theorem cyclicCoefficient_double (c : G → G → K)
    (hc : ∀ P Q R, c P Q + c (P + Q) R = c Q R + c P (Q + R))
    (T : G) (hT : IsOfFinAddOrder T) (k : ℕ) :
    cyclicCoefficient c T hT (2 * k) = 2 * cyclicCoefficient c T hT k +
      (addOrderOf T : K) * c (k • T) (k • T) := by
  simpa only [two_mul] using cyclicCoefficient_add c hc T hT k k

/-- The actual cyclic subgroup needs only the diagonal identities along that subgroup. -/
theorem cyclicCoefficient_double_of_diagonal (c : G → G → K)
    (T : G) (hT : IsOfFinAddOrder T) (k : ℕ)
    (hc : ∀ R : AddSubgroup.zmultiples T,
      c (k • T) (k • T) + c (k • T + k • T) R =
        c (k • T) R + c (k • T) (k • T + R)) :
    cyclicCoefficient c T hT (2 * k) = 2 * cyclicCoefficient c T hT k +
      (addOrderOf T : K) * c (k • T) (k • T) := by
  classical
  let := cyclicFintype T hT
  let c' : AddSubgroup.zmultiples T → AddSubgroup.zmultiples T → K :=
    fun P Q => c P Q
  let P : AddSubgroup.zmultiples T := ⟨k • T, ⟨(k : ℤ), by simp⟩⟩
  have hc' : ∀ R, c' P P + c' (P + P) R = c' P R + c' P (P + R) := by
    intro R
    exact hc R
  have hs := coefficient_double_of_diagonal c' P hc'
  simpa only [coefficient, rowSum, cyclicCoefficient, c', P,
    AddSubgroup.coe_add, two_mul, add_nsmul, cyclic_card T hT] using hs

end Cyclic

#print axioms translate_row_sum
#print axioms rowSum_add_of_identity
#print axioms rowSum_add
#print axioms coefficient_add_nsmul_of_identity
#print axioms coefficient_add_nsmul
#print axioms coefficient_zero
#print axioms coefficient_add
#print axioms coefficient_double
#print axioms coefficient_double_of_diagonal
#print axioms coefficientSequence_add
#print axioms coefficientSequence_double
#print axioms cyclic_card
#print axioms cyclicCoefficient_add
#print axioms cyclicCoefficient_double
#print axioms cyclicCoefficient_double_of_diagonal

end TRR08Geometry.FiniteSlopeAverage
