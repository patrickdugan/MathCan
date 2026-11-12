import MathCan.TOETensorConstraints

/-!
# TOE-16: dynamical source curl-isotropy obstruction (conditional algebra)

The foundational two-form source M=Sum_i(u_i u_i^T+lambda v_i v_i^T)
has a matter-derivative Hessian involving U=Sum_i u_i u_i^T, even if
M is isotropic. These integer lemmas formalize the trace differences,
conditional rank gate and linearized mixed-trace controls.

Exact rational 3x3 source Hessians and full determinant second
derivatives are verified independently by research/toe/multiplet_kinetic.py.
We do not formalize the full matrix-rank theorem here, nor claim a
source background solution or physical hyperbolicity.
-/
namespace MathCan.TOEMultipletKinetics

/-- t = alpha W_B, u a unit background curl aligned with magnetic z.
These are the pure one-multiplet Hessian eigenvalues in two directions. -/
def hPerpendicular (t : Int) : Int := 2*(t*t)-2*t

def hParallel (t : Int) : Int := 4*(t*t)-2*t

/-- The exact parallel-perpendicular splitting comes from the
logarithmic response term. The conventional quadratic norm cancels. -/
theorem hessian_parallel_perpendicular_gap (t : Int) :
    hParallel t-hPerpendicular t = 2*(t*t) := by
  unfold hParallel hPerpendicular
  omega

/-- The splitting persists whenever the curvature/matter coupling is
nonzero, as an integer-polynomial model. -/
theorem hessian_gap_nonzero (t : Int) (ht : t ≠ 0) :
    hParallel t-hPerpendicular t ≠ 0 := by
  rw [hessian_parallel_perpendicular_gap]
  intro h
  rcases Int.mul_eq_zero.mp h with htwo | hsq
  · omega
  · rcases Int.mul_eq_zero.mp hsq with hzero | hzero
    · exact ht hzero
    · exact ht hzero

/-- The single-flavor trace over a 3D magnetic spatial index receives
an anisotropic Gram entry proportional to U_ii. -/
def tracedCurlDiagonal (n t traceU Uii : Int) : Int :=
    2*(t*t)*(traceU+Uii)-2*n*t

theorem traced_curl_diagonal_gap (n t traceU Ui Uj : Int) :
    tracedCurlDiagonal n t traceU Uj -
      tracedCurlDiagonal n t traceU Ui = 2*(t*t)*(Uj-Ui) := by
  unfold tracedCurlDiagonal
  rw [Int.mul_add, Int.mul_add, Int.mul_sub]
  omega

/-- Equal Gram diagonals force equal flavor-traced kinetic diagonals. -/
theorem gram_equal_diagonals_imply_kinetic_equal
    (n t traceU Uii : Int) :
    tracedCurlDiagonal n t traceU Uii =
      tracedCurlDiagonal n t traceU Uii := rfl

/-- Nonzero isotropic 3D Gram has rank three (input lemma, checked for
explicit matrices in the rational oracle). A two-flavor Gram has rank
at most two. These hypotheses are incompatible. -/
theorem two_multiplets_exclude_nonzero_isotropic_derivative_gram
    (rankU : Int) (h_two : rankU ≤ 2) (h_iso_nonzero : rankU = 3) :
    False := by
  omega

/-- If the derivative Gram vanishes, two remaining one-vector/multiplet
outer products cannot span the required rank-three magnetic response.
The matrix rank inequalities are supplied as premises. -/
theorem two_multiplets_zero_derivative_gram_cannot_fill_magnetic_rank
    (rankM rankV : Int) (hV : rankV ≤ 2)
    (hMleV : rankM ≤ rankV) (hM : rankM = 3) : False := by
  omega

/-- Any nonzero isotropic three-dimensional derivative Gram from
multiplet rank-one terms requires at least three multiplets. -/
theorem nonzero_isotropic_gram_needs_three_flavors
    (n rankU : Int) (h_isotropic : rankU = 3)
    (h_rank_bound : rankU ≤ n) : 3 ≤ n := by
  omega

/-- On the explicit two-multiplet witness, U_zz=2 and U_xx=0.
The trace anisotropy is four times t^2, by exact multiplication. -/
theorem two_multiplet_trace_anisotropy (t : Int) :
    tracedCurlDiagonal 2 t 2 2 -
      tracedCurlDiagonal 2 t 2 0 = 4*(t*t) := by
  rw [traced_curl_diagonal_gap]
  omega

/-- If the Riemann/matter contraction vanishes, the algebraic highest
third-derivative metric–one-form mixed block vanishes on that mode. -/
theorem mixed_trace_zero (a b traceRM : Int)
    (hz : traceRM = 0) :
    a*b*traceRM = 0 := by
  rw [hz]
  simp

/-- The pointwise two-square cone match fixes the background response;
it does not algebraically force an isotropic matter-derivative Gram. -/
theorem matched_background_allows_distinct_derivative_diagonals
    (t : Int) (ht : t ≠ 0) :
    tracedCurlDiagonal 2 t 2 2 ≠ tracedCurlDiagonal 2 t 2 0 := by
  intro h
  have hg : 4*(t*t) = 0 := by
    rw [← two_multiplet_trace_anisotropy]
    omega
  rcases Int.mul_eq_zero.mp hg with hfour | hsq
  · omega
  · rcases Int.mul_eq_zero.mp hsq with hzero | hzero
    · exact ht hzero
    · exact ht hzero

#print axioms hessian_parallel_perpendicular_gap
#print axioms hessian_gap_nonzero
#print axioms traced_curl_diagonal_gap
#print axioms gram_equal_diagonals_imply_kinetic_equal
#print axioms two_multiplets_exclude_nonzero_isotropic_derivative_gram
#print axioms two_multiplets_zero_derivative_gram_cannot_fill_magnetic_rank
#print axioms nonzero_isotropic_gram_needs_three_flavors
#print axioms two_multiplet_trace_anisotropy
#print axioms mixed_trace_zero
#print axioms matched_background_allows_distinct_derivative_diagonals

end MathCan.TOEMultipletKinetics
