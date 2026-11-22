import Init

/-!
# BSAR-08: scale-homogeneous local BSA-R growth envelope

A sharpened local consequence of the Step 7 Leray-window premises:
for 0 < M, 0 <= I, 0 <= dnext, 2*I <= M, and
M*(dnext-dprev) <= I*dnext, one has

  M*dnext <= (M + 2*I)*dprev.

This is an integer cross-multiplied refinement of the factor-of-two
bound, valid under simultaneous rescaling of M and I. A family of
strict growth windows has arbitrarily small dimensionless I/M.
This module does not prove finite total I/M from Navier-Stokes dynamics.
-/

namespace MathCan.BSARRatioWindow

/-- The exact published BSA-R Step 7 local doubling argument. -/
theorem local_doubling
    (hM : 0 < M)
    (hnn : 0 ≤ dnext)
    (hode : M * (dnext - dprev) ≤ I * dnext)
    (hhalf : 2 * I ≤ M) :
    dnext ≤ 2 * dprev := by
  have htwice : 2 * (M * (dnext - dprev)) ≤ (2 * I) * dnext := by
    have hm := Int.mul_le_mul_of_nonneg_left hode (by omega : (0 : Int) ≤ 2)
    rw [← Int.mul_assoc 2 I dnext] at hm
    exact hm
  have hhalf_mul : (2 * I) * dnext ≤ M * dnext :=
    Int.mul_le_mul_of_nonneg_right hhalf hnn
  have hle : 2 * (M * (dnext - dprev)) ≤ M * dnext :=
    Int.le_trans htwice hhalf_mul
  have hrw : 2 * (M * (dnext - dprev)) = M * (2 * dnext - 2 * dprev) := by
    rw [Int.mul_sub M dnext dprev, Int.mul_sub 2 (M * dnext) (M * dprev),
        Int.mul_sub M (2 * dnext) (2 * dprev)]
    have s1 : 2 * (M * dnext) = M * (2 * dnext) := by
      rw [← Int.mul_assoc 2 M dnext, Int.mul_comm 2 M, Int.mul_assoc M 2 dnext]
    have s2 : 2 * (M * dprev) = M * (2 * dprev) := by
      rw [← Int.mul_assoc 2 M dprev, Int.mul_comm 2 M, Int.mul_assoc M 2 dprev]
    rw [s1, s2]
  rw [hrw] at hle
  by_cases h : dnext ≤ 2 * dprev
  · exact h
  · have hgt : dnext < 2 * dnext - 2 * dprev := by omega
    have hscaled := Int.mul_lt_mul_of_pos_left hgt hM
    omega

/-- One-step growth envelope with explicit dimensionless cost I/M.
    It retains much more information than the crude factor of two. -/
theorem refined_cross_multipled_envelope
    (hM : 0 < M)
    (hI : 0 ≤ I)
    (hnn : 0 ≤ dnext)
    (hode : M * (dnext - dprev) ≤ I * dnext)
    (hhalf : 2 * I ≤ M) :
    M * dnext ≤ (M + 2 * I) * dprev := by
  have hdouble : dnext ≤ 2 * dprev := local_doubling hM hnn hode hhalf
  have hupper : I * dnext ≤ I * (2 * dprev) :=
    Int.mul_le_mul_of_nonneg_left hdouble hI
  have hjoined : M * (dnext - dprev) ≤ I * (2 * dprev) :=
    Int.le_trans hode hupper
  have hleft : M * (dnext - dprev) = M * dnext - M * dprev := by
    rw [Int.mul_sub]
  have hright : I * (2 * dprev) = (2 * I) * dprev := by
    rw [← Int.mul_assoc I 2 dprev, Int.mul_comm I 2]
  rw [hleft, hright] at hjoined
  have hresult : (M + 2 * I) * dprev =
      M * dprev + (2 * I) * dprev := by
    rw [Int.add_mul]
  rw [hresult]
  omega

/-- Simultaneous positive rescaling of M and I preserves both
    local window inequalities; their meaningful quantity is I/M. -/
theorem scaled_window_constraints
    (hscale : 0 ≤ scale)
    (hode : M * (dnext - dprev) ≤ I * dnext)
    (hhalf : 2 * I ≤ M) :
    (scale * M) * (dnext - dprev) ≤ (scale * I) * dnext ∧
      2 * (scale * I) ≤ scale * M := by
  have hscaled_ode := Int.mul_le_mul_of_nonneg_left hode hscale
  have hscaled_half := Int.mul_le_mul_of_nonneg_left hhalf hscale
  constructor
  · simpa only [Int.mul_assoc] using hscaled_ode
  · have hrewrite : 2 * (scale * I) = scale * (2 * I) := by
      rw [← Int.mul_assoc 2 scale I, Int.mul_comm 2 scale,
          Int.mul_assoc scale 2 I]
    rw [hrewrite]
    exact hscaled_half

/-- Strict growth can satisfy the local source hypotheses while the
    positive cost I/M is at most 1/n, for arbitrarily large n.
    No universal dimensionless minimum growth charge follows. -/
theorem strict_growth_at_arbitrarily_small_relative_cost
    (n : Nat) (hn : 0 < n) :
    ∃ M I dprev dnext : Int,
      0 < M ∧ 0 ≤ I ∧ 0 ≤ dnext ∧
        2 * I ≤ M ∧ dprev < dnext ∧
        M * (dnext - dprev) ≤ I * dnext ∧
        (n : Int) * I ≤ M := by
  refine ⟨2 * (n : Int), 1, 2 * (n : Int) - 1, 2 * (n : Int),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hd : 2 * (n : Int) - (2 * (n : Int) - 1) = 1 := by omega
    rw [hd]
    simp
  · omega

end MathCan.BSARRatioWindow

#print axioms MathCan.BSARRatioWindow.local_doubling
#print axioms MathCan.BSARRatioWindow.refined_cross_multipled_envelope
#print axioms MathCan.BSARRatioWindow.scaled_window_constraints
#print axioms MathCan.BSARRatioWindow.strict_growth_at_arbitrarily_small_relative_cost
