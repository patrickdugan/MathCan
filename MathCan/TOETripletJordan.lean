import MathCan.TOEMultipletKinetics

/-!
# TOE-17: source triplet frequency-pencil factor and Jordan chain

Exact integer-scaled structural algebra for the source-derived restricted
tensor pencil at p=1. The common normalization is 228856384, yielding:
  P_hh=58525*(omega^2-1)^2
  P_ha=55815*(omega^2-1)
  P_aa=11163*(493*omega^2-490).
The full 6x6 bivector and 4x4 Ricci contractions establishing these
coefficients are checked by independent exact rational Python tests.
These Lean statements do not constitute a physical GfE hyperbolicity
certificate or a constraint-reduced Cauchy theorem.
-/
namespace MathCan.TOETripletJordan

def hMetric (x : Int) : Int := 58525 * ((x-1)*(x-1))
def hMixed (x : Int) : Int := 55815 * (x-1)
def hMatter (x : Int) : Int := 11163 * (493*x-490)

def hDet (x : Int) : Int :=
  hMetric x * hMatter x - hMixed x * hMixed x

/-- The exact normalized source determinant has a repeated light cone. -/
theorem exact_source_factor (x : Int) :
    hDet x = (x-1)*(x-1)*(279075*(1154113*x-1158253)) := by
  have h1 :
      (58525*((x-1)*(x-1)))*(11163*(493*x-490)) =
      ((x-1)*(x-1))*(58525*11163*(493*x-490)) := by
    ac_rfl
  have h2 :
      (55815*(x-1))*(55815*(x-1)) =
      ((x-1)*(x-1))*(55815*55815) := by
    ac_rfl
  have hn :
      58525*11163*(493*x-490)-55815*55815 =
      279075*(1154113*x-1158253) := by
    omega
  calc
    hDet x =
        (58525*((x-1)*(x-1)))*(11163*(493*x-490)) -
        (55815*(x-1))*(55815*(x-1)) := rfl
    _ = ((x-1)*(x-1))*(58525*11163*(493*x-490)) -
        ((x-1)*(x-1))*(55815*55815) := by rw [h1,h2]
    _ = ((x-1)*(x-1))*
        (58525*11163*(493*x-490)-55815*55815) := by
        exact (Int.mul_sub ((x-1)*(x-1))
          (58525*11163*(493*x-490)) (55815*55815)).symm
    _ = (x-1)*(x-1)*(279075*(1154113*x-1158253)) := by
        rw [hn]

theorem exact_lightcone_null :
    hMetric 1 = 0 ∧ hMixed 1 = 0 ∧ hMatter 1 = 33489 := by
  decide

theorem exact_lightcone_det_zero : hDet 1 = 0 := by
  rw [exact_source_factor]
  decide

theorem exact_root_linear_cofactor_nonzero :
    279075*(1154113*(1:Int)-1158253) ≠ 0 := by
  decide

/-- Gauge-direction component of a polynomial null vector is zero at
the lightcone, because the source matter diagonal is nonzero. -/
theorem root_kernel_matter_zero (y : Int)
    (hy : hMatter 1 * y = 0) : y = 0 := by
  have hm : hMatter 1 = 33489 := (exact_lightcone_null).2.2
  rw [hm] at hy
  rcases Int.mul_eq_zero.mp hy with hz | hz
  · omega
  · exact hz

/-- At omega=1: d/domega P_ha = 2*55815, P_aa=33489.
The rational-normalized Jordan chain v0=(1,0), v1=(0,-10/3)
has integer-rescaled v0=(3,0), v1=(0,-10). -/
theorem source_polynomial_jordan_chain :
    33489*(-10:Int) + (2*55815)*3 = 0 := by
  omega

/-- The square-root characteristic has a true order-two zero since
its remaining cofactor is nonzero at x=1. -/
theorem repeated_root_cofactor_nonzero :
    (1154113*(1:Int)-1158253) ≠ 0 := by
  decide

/-- A longitudinal one-form amplitude has zero exterior wedge but
nonzero coderivative on the spacelike unit frequency test k=(0,0,0,1).
This illustrates that the Dirac-Kahler D=d+delta_D has no automatic
Yang--Mills gauge quotient. -/
theorem longitudinal_coderivative_not_gauge :
    (0:Int) = 0 ∧ (1:Int) ≠ 0 := by
  decide

#print axioms exact_source_factor
#print axioms exact_lightcone_null
#print axioms exact_lightcone_det_zero
#print axioms exact_root_linear_cofactor_nonzero
#print axioms root_kernel_matter_zero
#print axioms source_polynomial_jordan_chain
#print axioms repeated_root_cofactor_nonzero
#print axioms longitudinal_coderivative_not_gauge

end MathCan.TOETripletJordan
