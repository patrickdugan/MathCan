import MathCan.TOEJordan

/-!
# TOE-13: scalar/vector curvature response and a lifted tensor root

This is kernel-level algebra in the *declared* flat-background 0/1/2-form
logarithmic principal completion of the TOE-12 6-mode tensor model.
The 4x4 Ricci principal, G-field algebraic Schur elimination, and rational
6-mode determinant are checked by independent executable oracles.

These integer lemmas do not formalize the full Lambda-GfE covariant action,
its constraint-reduced PDE, a physical dispersion relation or hyperbolicity.
-/
namespace MathCan.TOEFormSectors

/-- The scalar-curvature principal of an isolated transverse-traceless wave
has opposite spatial diagonal entries and vanishing trace. -/
def ttRicciTrace (a : Int) : Int := a + (-a)

theorem tt_ricci_scalar_zero (a : Int) : ttRicciTrace a = 0 := by
  unfold ttRicciTrace
  omega

/-- Consequently the quadratic 0-form scalar-log response vanishes for an
isolated TT variation at fourth differential order. -/
theorem scalar_sector_tt_zero (beta invScalar a : Int) :
    (beta * invScalar) * (ttRicciTrace a) * (ttRicciTrace a) = 0 := by
  rw [tt_ricci_scalar_zero]
  simp

/-- Both independent TT helicities receive the same one-form quartic kernel.
At formal wave covector (omega,0,0,p), the integer-normalized polynomial
is k*(omega²-p²)², with all normalization encoded in k. -/
def vectorTT (k omega2 p2 : Int) : Int :=
  k * ((omega2-p2)*(omega2-p2))

theorem vector_tt_on_lightcone (k x : Int) : vectorTT k x x = 0 := by
  simp [vectorTT]

/-- The transverse-traceless one-form response has zero plus/cross mixing
in the isotropic frozen background: the metric subblock is diagonal. -/
def metricTTDet (vplus vcross : Int) : Int := vplus * vcross

theorem equal_helicity_det (v : Int) : metricTTDet v v = v*v := rfl

/-- The lifted old tensor root has a two-helicity metric determinant times
the independent four-gauge-mode determinant. -/
def liftedDet (k q gaugeDet : Int) : Int := (k*q)*(k*q)*gaugeDet

theorem lifted_det_factor (k q gaugeDet : Int) :
    liftedDet k q gaugeDet = (k*k)*(q*q)*gaugeDet := by
  unfold liftedDet
  have h : (k*q)*(k*q) = (k*k)*(q*q) := by ac_rfl
  rw [h]

/-- A nonzero one-form coefficient and a non-lightcone old root force a
nonzero metric entry. -/
theorem nonzero_vector_root_entry (k q : Int)
    (hk : k ≠ 0) (hq : q ≠ 0) : k*q ≠ 0 := by
  intro h
  rcases Int.mul_eq_zero.mp h with h0 | h0
  · exact hk h0
  · exact hq h0

/-- Algebraic certificate underlying the exact Q(sqrt(r)) determinant test:
two lifted metric helicities and an invertible gauge block have nonzero
block determinant. -/
theorem nonzero_lifted_det (k q gaugeDet : Int)
    (hk : k ≠ 0) (hq : q ≠ 0) (hg : gaugeDet ≠ 0) :
    liftedDet k q gaugeDet ≠ 0 := by
  unfold liftedDet
  have hp : k*q ≠ 0 := nonzero_vector_root_entry k q hk hq
  intro h
  rcases Int.mul_eq_zero.mp h with hmetric | hgauge
  · rcases Int.mul_eq_zero.mp hmetric with hleft | hright
    · exact hp hleft
    · exact hp hright
  · exact hg hgauge

/-- No nonzero metric amplitude lies in the diagonal lifted TT block. -/
theorem lifted_tt_no_kernel (k q x : Int)
    (hk : k ≠ 0) (hq : q ≠ 0)
    (hx : (k*q)*x = 0) : x = 0 := by
  have hp : k*q ≠ 0 := nonzero_vector_root_entry k q hk hq
  rcases Int.mul_eq_zero.mp hx with hzero | hxzero
  · exact False.elim (hp hzero)
  · exact hxzero

/-- With two TT polarizations, invertibility of each lifted entry removes
both old metric null directions in the block-restricted model. -/
theorem two_helicity_kernel_removed (k q x y : Int)
    (hk : k ≠ 0) (hq : q ≠ 0)
    (hx : (k*q)*x = 0) (hy : (k*q)*y = 0) :
    x = 0 ∧ y = 0 := by
  exact ⟨lifted_tt_no_kernel k q x hk hq hx,
         lifted_tt_no_kernel k q y hk hq hy⟩

#print axioms tt_ricci_scalar_zero
#print axioms scalar_sector_tt_zero
#print axioms vector_tt_on_lightcone
#print axioms equal_helicity_det
#print axioms lifted_det_factor
#print axioms nonzero_vector_root_entry
#print axioms nonzero_lifted_det
#print axioms lifted_tt_no_kernel
#print axioms two_helicity_kernel_removed
end MathCan.TOEFormSectors
