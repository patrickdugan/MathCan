import MathCan.BSARRatioWindow

/-!
# BSAR-09: exact finite-product certificate for the source-aligned window rule

The original BSA-R Step7 local ODE and half-budget assumptions imply
  M*dnext <= (M + 2*I)*dprev
under M>0, I>=0 and dnext>=0 (BSAR-08).

This module composes K such windows without converting I/M to an
integer event count. It records the exact numerator and denominator
of the finite rational product:
    denominator = product (M over all windows)
    numerator   = product (M + 2*I_m over all windows)

The theorem below proves
    denominator * dlast <= numerator * d0
for every finite K, with a positive denominator.

No statement about a uniform bound over all K or physical Navier-Stokes
regularity follows until a separate bound on the ratio product is supplied.
-/

namespace MathCan.BSARFiniteProduct

/-- Source-aligned, finite chain carrying the cross-multiplied product
certificate; the source remains a fixed positive integer M. -/
inductive RatioProductChain (M : Int) :
    Nat → Int → Int → Int → Int → Prop
  | refl (d0 : Int) :
      RatioProductChain M 0 d0 d0 1 1
  | step {k : Nat} {d0 dm dnext denom numer I : Int}
      (hprev : RatioProductChain M k d0 dm denom numer)
      (hM : 0 < M)
      (hI : 0 ≤ I)
      (hnext : 0 ≤ dnext)
      (hode : M * (dnext - dm) ≤ I * dnext)
      (hhalf : 2 * I ≤ M) :
      RatioProductChain M (k + 1) d0 dnext
        (denom * M) (numer * (M + 2 * I))

/-- The exact rational product certificate remains valid as K increases.
The numerator and denominator are positive/nonnegative by construction. -/
theorem certificate
    (hchain : RatioProductChain M k d0 dfinal denom numer) :
    0 < denom ∧ 0 ≤ numer ∧ denom * dfinal ≤ numer * d0 := by
  induction hchain with
  | refl d =>
      constructor
      · decide
      constructor
      · decide
      · simp
  | @step k d0 dm dnext den num I hprev hM hI hnext hode hhalf ih =>
      obtain ⟨hden, hnum, hbound⟩ := ih
      have hfactor : 0 ≤ M + 2 * I := by omega
      have hdennext : 0 < den * M := Int.mul_pos hden hM
      have hnumnext : 0 ≤ num * (M + 2 * I) :=
        Int.mul_nonneg hnum hfactor
      have hlocal : M * dnext ≤ (M + 2 * I) * dm :=
        BSARRatioWindow.refined_cross_multiplied_envelope
          hM hI hnext hode hhalf
      have hleft : den * (M * dnext) ≤ den * ((M + 2 * I) * dm) :=
        Int.mul_le_mul_of_nonneg_left hlocal (by omega)
      have hright :
          (M + 2 * I) * (den * dm) ≤ (M + 2 * I) * (num * d0) :=
        Int.mul_le_mul_of_nonneg_left hbound hfactor
      refine ⟨hdennext, hnumnext, ?_⟩
      calc
        (den * M) * dnext = den * (M * dnext) := by rw [Int.mul_assoc]
        _ ≤ den * ((M + 2 * I) * dm) := hleft
        _ = (M + 2 * I) * (den * dm) := by
          rw [← Int.mul_assoc den (M + 2 * I) dm,
            Int.mul_comm den (M + 2 * I),
            Int.mul_assoc (M + 2 * I) den dm]
        _ ≤ (M + 2 * I) * (num * d0) := hright
        _ = (num * (M + 2 * I)) * d0 := by
          rw [← Int.mul_assoc (M + 2 * I) num d0,
            Int.mul_comm (M + 2 * I) num]

/-- The source local assumptions give a multiplicative bound rather
than a horizon-independent one. A later lemma needs an aggregate ratio
budget on numerator/denominator to infer a uniform endpoint cap. -/
theorem endpoint_cross_multiplied
    (hchain : RatioProductChain M k d0 dfinal denom numer) :
    denom * dfinal ≤ numer * d0 :=
  (certificate hchain).2.2

/-- A second, independently supplied bound for the exact product is
sufficient for a global endpoint certificate. Positivity of denom is
retained for subsequent rational-domain interpretation. -/
theorem budgeted_cross_multiplied
    (hchain : RatioProductChain M k d0 dfinal denom numer)
    (h0 : 0 ≤ d0)
    (hbudget : numer ≤ budget * denom)
    (hbudget_nonneg : 0 ≤ budget) :
    denom * dfinal ≤ (budget * denom) * d0 := by
  have hbase := endpoint_cross_multiplied hchain
  have hscaled := Int.mul_le_mul_of_nonneg_right hbudget h0
  exact Int.le_trans hbase hscaled

end MathCan.BSARFiniteProduct

#print axioms MathCan.BSARFiniteProduct.certificate
#print axioms MathCan.BSARFiniteProduct.endpoint_cross_multiplied
#print axioms MathCan.BSARFiniteProduct.budgeted_cross_multiplied
