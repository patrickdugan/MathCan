module

public import MathCan.TranslationInterpolationUniform

/-!
# TRR-08: root counting for the uniform interpolation obstruction

This module implements finite Horner polynomials and proves their root bound by
synthetic division. It connects distinct evaluations of the actual degree-eight
obstruction to the coefficient classification in TRR-07. Geometric inputs remain
explicit: the field elements must arise from the residue and doubling identities.
-/

set_option maxHeartbeats 2000000

@[expose] public section

namespace MathCan.TranslationInterpolationRootBound

open Lean.Grind
open MathCan.TranslationInterpolationUniform

variable {K : Type} [Field K]

/-- A coefficient list is ordered from its constant coefficient upward. -/
def evaluate : List K → K → K
  | [], _ => 0
  | c :: cs, x => c + x * evaluate cs x

/-- The quotient of a finite Horner polynomial by `X-a`. -/
def syntheticQuotient (a : K) : List K → List K
  | [] => []
  | _ :: [] => []
  | _ :: c :: cs => evaluate (c :: cs) a :: syntheticQuotient a (c :: cs)

def ZeroCoefficients : List K → Prop
  | [] => True
  | c :: cs => c = 0 ∧ ZeroCoefficients cs

theorem evaluate_quotient_cons (a c x : K) (cs : List K) :
    evaluate (syntheticQuotient a (c :: cs)) x =
      evaluate cs a + x * evaluate (syntheticQuotient a cs) x := by
  cases cs with
  | nil => simp [syntheticQuotient, evaluate]; grind
  | cons d ds => rfl

/-- Synthetic division, including its actual evaluation remainder. -/
theorem synthetic_division (p : List K) (a x : K) :
    evaluate p x = evaluate p a + (x-a) * evaluate (syntheticQuotient a p) x := by
  induction p with
  | nil => simp [evaluate, syntheticQuotient]; grind
  | cons c cs ih =>
      rw [evaluate_quotient_cons]
      simp only [evaluate]
      grind

theorem quotient_length (a c : K) (cs : List K) :
    (syntheticQuotient a (c :: cs)).length = cs.length := by
  induction cs generalizing c with
  | nil => rfl
  | cons d ds ih =>
      simp only [syntheticQuotient, List.length_cons]
      rw [ih]

/-- A zero remainder and a zero quotient force every original coefficient to vanish. -/
theorem zero_of_quotient (p : List K) (a : K)
    (hr : evaluate p a = 0) (hq : ZeroCoefficients (syntheticQuotient a p)) :
    ZeroCoefficients p := by
  induction p with
  | nil => trivial
  | cons c cs ih =>
      cases cs with
      | nil =>
          simp only [evaluate] at hr
          exact ⟨by grind, True.intro⟩
      | cons d ds =>
          change evaluate (d :: ds) a = 0 ∧
            ZeroCoefficients (syntheticQuotient a (d :: ds)) at hq
          have ht := ih hq.1 hq.2
          change c + a * evaluate (d :: ds) a = 0 at hr
          exact ⟨by grind, ht⟩

/-- A polynomial with at most `m` coefficients vanishing at `m` distinct field
elements has all coefficients zero. This includes trailing zero coefficients. -/
theorem coefficients_zero_of_distinct_roots (roots p : List K)
    (hdistinct : roots.Nodup) (hlen : p.length ≤ roots.length)
    (hzero : ∀ x, x ∈ roots → evaluate p x = 0) :
    ZeroCoefficients p := by
  induction roots generalizing p with
  | nil =>
      cases p with
      | nil => trivial
      | cons c cs => simp at hlen
  | cons a roots ih =>
      cases p with
      | nil => trivial
      | cons c cs =>
          have hd := List.nodup_cons.mp hdistinct
          have hr := hzero a List.mem_cons_self
          have hquot : ∀ x, x ∈ roots →
              evaluate (syntheticQuotient a (c :: cs)) x = 0 := by
            intro x hx
            have hp := hzero x (List.mem_cons_of_mem a hx)
            have hdiv := synthetic_division (c :: cs) a x
            have hprod : (x-a)*evaluate (syntheticQuotient a (c :: cs)) x = 0 := by
              grind
            cases Field.of_mul_eq_zero hprod with
            | inr hz => exact hz
            | inl hz =>
                have he : x = a := by grind
                exact False.elim (hd.1 (he ▸ hx))
          have hsize : (syntheticQuotient a (c :: cs)).length ≤ roots.length := by
            rw [quotient_length]
            simp only [List.length_cons] at hlen
            omega
          exact zero_of_quotient (c :: cs) a hr (ih _ hd.2 hsize hquot)

/-- The exact degree-eight obstruction from the written doubling argument. -/
def obstruction (n A B c x : K) : K :=
  (4*(6*x+3*c)*(x^3+A*x+B)+(n-1)*(3*x^2+A)^2)^2 -
    64*n*(x+c)*(3*x^2+A)^2*(x^3+A*x+B)

/-- All nine coefficients, with the constant coefficient first. Their equality
to the displayed obstruction is checked over an arbitrary field below. -/
def obstructionCoefficients (n A B c : K) : List K :=
  [ A^4*n^2-2*A^4*n+A^4-40*A^2*B*c*n-24*A^2*B*c+144*B^2*c^2,
    -40*A^3*c*n-24*A^3*c-16*A^2*B*n-48*A^2*B+288*A*B*c^2+576*B^2*c,
    12*A^3*n^2-40*A^3*n-36*A^3+144*A^2*c^2-240*A*B*c*n+1008*A*B*c+576*B^2,
    -280*A^2*c*n+408*A^2*c-96*A*B*n+864*A*B+288*B*c^2,
    54*A^2*n^2-220*A^2*n+294*A^2+288*A*c^2-360*B*c*n+936*B*c,
    -600*A*c*n+792*A*c-144*B*n+720*B,
    108*A*n^2-456*A*n+540*A+144*c^2,
    -360*c*n+360*c,
    81*n^2-306*n+225 ]

theorem obstruction_evaluation (n A B c x : K) :
    evaluate (obstructionCoefficients n A B c) x = obstruction n A B c x := by
  simp only [evaluate, obstructionCoefficients, obstruction]
  grind

/-- Nine distinct roots of the actual obstruction imply a singular cubic.
The coefficient equalities are conclusions of synthetic division, not hypotheses. -/
theorem obstruction_roots_force_singularity (n A B c : K) (roots : List K)
    (hn : n ≠ 0) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hdistinct : roots.Nodup) (hlen : 9 ≤ roots.length)
    (hzero : ∀ x, x ∈ roots → obstruction n A B c x = 0) :
    4*A^3+27*B^2 = 0 := by
  have hz := coefficients_zero_of_distinct_roots roots (obstructionCoefficients n A B c)
    hdistinct (by simpa [obstructionCoefficients] using hlen)
    (by intro x hx; rw [obstruction_evaluation]; exact hzero x hx)
  simp only [ZeroCoefficients, obstructionCoefficients] at hz
  have h5 := hz.2.2.2.2.2.1
  have h6 := hz.2.2.2.2.2.2.1
  have h7 := hz.2.2.2.2.2.2.2.1
  have h8 := hz.2.2.2.2.2.2.2.2.1
  apply leading_coefficients_force_singularity n A B c hn h₂ h₃
  · grind
  · grind
  · exact h6
  · exact h5

theorem nonsingular_obstruction_root_exclusion (n A B c : K) (roots : List K)
    (hn : n ≠ 0) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hsmooth : 4*A^3+27*B^2 ≠ 0)
    (hdistinct : roots.Nodup) (hlen : 9 ≤ roots.length) :
    ¬ (∀ x, x ∈ roots → obstruction n A B c x = 0) := by
  intro hzero
  exact hsmooth (obstruction_roots_force_singularity n A B c roots hn h₂ h₃
    hdistinct hlen hzero)

/-- The doubling and residue identities imply an actual root of the
obstruction. All denominators have already been cleared in the tangent identity. -/
theorem doubling_implies_obstruction (n A B c x y a m x₂ a₂ : K)
    (hn : n ≠ 0)
    (hcurve : x^3+A*x+B = y^2)
    (htangent : 3*x^2+A = 2*y*m)
    (hx₂ : x₂ = m^2-2*x)
    (ha₂ : a₂ = 2*a+n*m)
    (hnorm : a^2 = n*(x+c))
    (hnorm₂ : a₂^2 = n*(x₂+c)) :
    obstruction n A B c x = 0 := by
  have hz : n*(4*a*m+6*x+3*c+(n-1)*m^2) = 0 := by grind
  have hline := cancel_nonzero hn hz
  have hsquare : (6*x+3*c+(n-1)*m^2)^2 = 16*n*(x+c)*m^2 := by
    have he : 6*x+3*c+(n-1)*m^2 = -(4*a*m) := by grind
    calc
      (6*x+3*c+(n-1)*m^2)^2 = (-(4*a*m))^2 := congrArg (fun z : K => z^2) he
      _ = 16*a^2*m^2 := by grind
      _ = 16*(n*(x+c))*m^2 := by rw [hnorm]
      _ = 16*n*(x+c)*m^2 := by grind
  have hscaled := congrArg (fun z : K => 16*y^4*z) hsquare
  unfold obstruction
  rw [hcurve, htangent]
  clear hn hcurve htangent hx₂ ha₂ hnorm hnorm₂ hz hline hsquare
  grind

/-- The entire tame algebraic obstruction from distinct coordinates and the
explicit pointwise doubling data. No root or coefficient condition is assumed. -/
theorem doubling_data_force_singularity (n A B c : K) (roots : List K)
    (hn : n ≠ 0) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hdistinct : roots.Nodup) (hlen : 9 ≤ roots.length)
    (hdata : ∀ x, x ∈ roots → ∃ y a m x₂ a₂ : K,
      x^3+A*x+B = y^2 ∧
      3*x^2+A = 2*y*m ∧
      x₂ = m^2-2*x ∧
      a₂ = 2*a+n*m ∧
      a^2 = n*(x+c) ∧
      a₂^2 = n*(x₂+c)) :
    4*A^3+27*B^2 = 0 := by
  apply obstruction_roots_force_singularity n A B c roots hn h₂ h₃ hdistinct hlen
  intro x hx
  obtain ⟨y, a, m, x₂, a₂, hc, ht, hx₂, ha₂, ha, ha₂norm⟩ := hdata x hx
  exact doubling_implies_obstruction n A B c x y a m x₂ a₂ hn hc ht hx₂ ha₂ ha ha₂norm

theorem nonsingular_doubling_data_exclusion (n A B c : K) (roots : List K)
    (hn : n ≠ 0) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hsmooth : 4*A^3+27*B^2 ≠ 0)
    (hdistinct : roots.Nodup) (hlen : 9 ≤ roots.length) :
    ¬ (∀ x, x ∈ roots → ∃ y a m x₂ a₂ : K,
      x^3+A*x+B = y^2 ∧
      3*x^2+A = 2*y*m ∧
      x₂ = m^2-2*x ∧
      a₂ = 2*a+n*m ∧
      a^2 = n*(x+c) ∧
      a₂^2 = n*(x₂+c)) := by
  intro hdata
  exact hsmooth (doubling_data_force_singularity n A B c roots hn h₂ h₃
    hdistinct hlen hdata)

#print axioms evaluate_quotient_cons
#print axioms synthetic_division
#print axioms quotient_length
#print axioms zero_of_quotient
#print axioms coefficients_zero_of_distinct_roots
#print axioms obstruction_evaluation
#print axioms obstruction_roots_force_singularity
#print axioms nonsingular_obstruction_root_exclusion
#print axioms doubling_implies_obstruction
#print axioms doubling_data_force_singularity
#print axioms nonsingular_doubling_data_exclusion

end MathCan.TranslationInterpolationRootBound
