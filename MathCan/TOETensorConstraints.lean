import MathCan.TOEConeMatching

/-!
# TOE-15: algebraic multi-form cone compensation and little-group gates

Kernel-level integer algebra for the source-structured matter curvature
matching condition and a rank-optimal two-multiplet quadratic witness.
The six-by-six rational SO(2) commutator, Hermitian three-by-three
determinant, rank-three witness, and G-field Schur are independently
tested by the Python oracle. The complete coupled source action,
background field equations and constrained first-order Cauchy system
are not formalized here.
-/
namespace MathCan.TOETensorConstraints

/-- Common-denominator E/B response eigenvalue numerators. -/
def thetaElectric (s alpha beta accel matterE : Int) : Int :=
  s + alpha*matterE - (2*beta)*accel

def thetaMagnetic (s alpha beta spatial matterB : Int) : Int :=
  s + alpha*matterB - (2*beta)*spatial

/-- Exact source Eq. (40) at the level of common-denominator integer
response eigenvalues. No field background equations are assumed. -/
theorem source_cone_match_iff_compensation
    (s alpha beta accel spatial matterE matterB : Int) :
    thetaElectric s alpha beta accel matterE =
      thetaMagnetic s alpha beta spatial matterB ↔
        alpha*(matterE-matterB) = (2*beta)*(accel-spatial) := by
  unfold thetaElectric thetaMagnetic
  rw [Int.mul_sub, Int.mul_sub]
  omega

/-- Two rank-at-most-two multiplets are first allowed to supply an
isotropic response of rank three by the elementary rank upper bound. -/
theorem rank_three_needs_two_multiplets
    (n : Int) (hn : 0 ≤ n) (hr : 3 ≤ 2*n) : 2 ≤ n := by
  omega

theorem one_multiplet_cannot_have_rank_three (r : Int)
    (hr : r ≤ 2) : r ≠ 3 := by
  omega

/-- Four rank-one terms with coefficient lambda=2:
D1=e_z, phi1=e_x; D2=e_z, phi2=e_y. -/
def twoMultipletQuadratic (x y z : Int) : Int :=
  z*z + 2*x*x + z*z + 2*y*y

/-- Their sum is the isotropic quadratic response 2 I_3. -/
theorem two_multiplet_magnetic_isotropic (x y z : Int) :
    twoMultipletQuadratic x y z = 2*(x*x+y*y+z*z) := by
  unfold twoMultipletQuadratic
  rw [Int.mul_add, Int.mul_add]
  simp only [Int.mul_assoc]
  omega

/-- Rescaled exact compensation at the pinned FLRW reference:
alpha=3/500, beta=1/100, accel=2/5, spatial=1, mE=0, mB=2. -/
theorem two_multiplet_reference_compensation :
    (3*5 : Int)*(0-2) = (2*5)*(2-5) := by
  omega

/-- On a cone-matched background, any nonzero response detuning
changes its affine E/B eigenvalue. -/
theorem nonzero_magnetic_detuning_changes_response
    (theta alpha detuning : Int)
    (ha : alpha ≠ 0) (hd : detuning ≠ 0) :
    theta + alpha*detuning ≠ theta := by
  intro h
  have hp : alpha*detuning = 0 := by omega
  rcases Int.mul_eq_zero.mp hp with h0 | h0
  · exact ha h0
  · exact hd h0

/-- The 2x2 real spin-two block [[a,b],[-b,a]] commutes with
J=[[0,-1],[1,0]]. This is the componentwise upper-right equality. -/
theorem helicity_block_commutator_upper_right (a b : Int) :
    a*(-1)+b*0 = 0*b + (-1)*a := by omega

theorem helicity_block_commutator_lower_left (a b : Int) :
    (-b)*0+a*1 = 1*a+0*(-b) := by omega

#print axioms source_cone_match_iff_compensation
#print axioms rank_three_needs_two_multiplets
#print axioms one_multiplet_cannot_have_rank_three
#print axioms two_multiplet_magnetic_isotropic
#print axioms two_multiplet_reference_compensation
#print axioms nonzero_magnetic_detuning_changes_response
#print axioms helicity_block_commutator_upper_right
#print axioms helicity_block_commutator_lower_left

end MathCan.TOETensorConstraints
