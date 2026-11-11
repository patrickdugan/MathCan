import Init

/-!
# TOE-07: Algebraic response compensation and homogeneous scalar obstruction

These are *algebraic* kernel lemmas in the declared isotropic response model.
They do not construct a microscopic GfE two-multiplet matter action and they
do not prove the full dressed covariant field equations or hyperbolicity.

Source context: Pereira (2026), arXiv:2609.03082, tensor-characteristic
and rank conditions; Bianconi (2026), arXiv:2610.34496, induced metric.
-/
namespace MathCan.TOETensorCompletion

/-- The positive response budget for a signed target difference. -/
def positivePart (d : Int) : Int := if 0 ≤ d then d else 0

/-- The negative response budget, represented as a nonnegative number. -/
def negativePart (d : Int) : Int := if 0 ≤ d then 0 else -d

theorem positivePart_nonnegative (d : Int) : 0 ≤ positivePart d := by
  by_cases h : 0 ≤ d
  · simp [positivePart, h]
  · simp [positivePart, h]

theorem negativePart_nonnegative (d : Int) : 0 ≤ negativePart d := by
  by_cases h : 0 ≤ d
  · simp [negativePart, h]
  · simp [negativePart, h]
    omega

/-- Every signed isotropic E/B response mismatch can be cancelled by two
    nonnegative *effective scalar response values*. This is a pointwise
    feasibility result with the field-realization gate left open. -/
theorem signed_response_decomposition (d : Int) :
    positivePart d - negativePart d = d := by
  by_cases h : 0 ≤ d
  · simp [positivePart, negativePart, h]
  · simp [positivePart, negativePart, h]

/-- A common baseline preserves the desired signed response difference. -/
theorem baseline_preserves_split (mE mB baseline d : Int)
    (h : mE - mB = d) :
    (mE + baseline) - (mB + baseline) = d := by
  omega

/-- An algebraic equality of curvature and source shifts closes the split. -/
theorem matched_inverse_response (curvatureShift sourceShift : Int)
    (h : curvatureShift = sourceShift) :
    sourceShift - curvatureShift = 0 := by
  omega

/-- A strictly nonzero split excludes equality of the two induced responses. -/
theorem mismatched_inverse_response (curvatureShift sourceShift : Int)
    (h : sourceShift - curvatureShift ≠ 0) :
    sourceShift ≠ curvatureShift := by
  intro heq
  exact h (by omega)

/-- In the model with nonzero alpha, the necessary algebraic matching
    condition can be expressed as equality between the source and curvature
    response products. -/
def sourceMinusCurvature (source curvature : Int) : Int :=
  source - curvature

theorem zero_gap_of_equal_products (source curvature : Int)
    (h : source = curvature) :
    sourceMinusCurvature source curvature = 0 := by
  simp [sourceMinusCurvature, h]

/-- Purely time-directed homogeneous one-forms on a four-dimensional frame. -/
def temporal (x : Int) (i : Fin 4) : Int :=
  if i.val = 0 then x else 0

/-- Wedge product of two one-forms, evaluated on indices i,j. -/
def wedge (a b : Fin 4 → Int) (i j : Fin 4) : Int :=
  a i * b j - a j * b i

/-- Any two homogeneous scalar gradients have zero antisymmetric wedge,
    independent of the number of scalar species considered. -/
theorem homogeneous_scalar_wedge_zero (u v : Int) (i j : Fin 4) :
    wedge (temporal u) (temporal v) i j = 0 := by
  unfold wedge temporal
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · simp [hi, hj]
    · simp [hi, hj]
  · by_cases hj : j.val = 0
    · simp [hi, hj]
    · simp [hi, hj]

/-- A specific isotropic Ricci-response *completion* has equal electric and
    spatial response coefficients in the linear GR limit. Numerators of 6U,
    6V are used to stay in integer algebra. -/
def sixU (fA fB : Int) : Int := 2*fA - fB
def sixV (_fA fB : Int) : Int := fB

theorem gr_ricci_response_equal (f : Int) : sixU f f = sixV f f := by
  simp [sixU, sixV]
  omega

/-- The FLRW Ricci derivative operator on P^00=-U, P^ij=Vg^ij,
    multiplied by two to avoid fractions. S=Hdot+3H^2. -/
def twiceRicciD00 (H S U V Ud Vd : Int) : Int :=
  3*((U-V)*S + H*(Ud+Vd))

def twiceRicciDs (H S U V Ud Udd Vdd : Int) : Int :=
  -(U-V)*S-(Udd+Vdd)-4*(H*Ud)

/-- Standard f(R) temporal derivative contribution for U=V=f_R. -/
theorem fr_temporal_limit (H S f fd : Int) :
    twiceRicciD00 H S f f fd fd = 6*(H*fd) := by
  simp [twiceRicciD00, Int.mul_add]
  omega

/-- Standard f(R) spatial derivative contribution for U=V=f_R. -/
theorem fr_spatial_limit (H S f fd fdd : Int) :
    twiceRicciDs H S f f fd fdd fdd = -2*fdd-4*(H*fd) := by
  simp [twiceRicciDs]
  omega

/-- A constant metric-proportional Ricci response gives no derivative tensor. -/
theorem einstein_derivative_vanishes (H S f : Int) :
    twiceRicciD00 H S f f 0 0 = 0 ∧
    twiceRicciDs H S f f 0 0 0 = 0 := by
  constructor <;> simp [twiceRicciD00, twiceRicciDs]

#print axioms positivePart_nonnegative
#print axioms negativePart_nonnegative
#print axioms signed_response_decomposition
#print axioms baseline_preserves_split
#print axioms matched_inverse_response
#print axioms mismatched_inverse_response
#print axioms zero_gap_of_equal_products
#print axioms homogeneous_scalar_wedge_zero
#print axioms gr_ricci_response_equal
#print axioms fr_temporal_limit
#print axioms fr_spatial_limit
#print axioms einstein_derivative_vanishes
end MathCan.TOETensorCompletion
