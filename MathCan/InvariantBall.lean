import Init

/-!
# NOR-04: source-locked invariant-ball arithmetic

The real analytic fixed-point theorem in research/nor04 is paper-level.
This Init-only module kernel-checks the integer clearance identity from
the source-locked RRC25 numerical certificate and a scaled
nonlinear-invariance budget implication.

Theorem nor04_margin_exact uses the exact residual and uniform Jacobian
fractions from the independent GitHub Actions rational interval artifact.
It is not a proof that those fractions enclose the transcendental GRU:
that is checked by the separate rational interval program.
-/
namespace MathCan.InvariantBall

/-- Exact integer clearance from the machine-generated rational receipt:
s=237277631/(2*10^23), K=928242792263/10^12,
R=1/10^11. Multiplying s+KR<=R by 2*10^23 gives this. -/
theorem nor04_margin_exact :
    237277631 + 2 * 928242792263 ≤ 2000000000000 := by
  decide

/-- The exact positive numerator of the invariant margin. -/
theorem nor04_margin_numerator :
    2000000000000 - (237277631 + 2 * 928242792263) =
      143277137843 := by
  decide

/-- Fixed-point ball arithmetic for a rational coefficient
K=928242792263/10^12. Given a scaled one-step map bound,
a radius clearance guarantees that the next point remains in
the radius. This is a finite arithmetic analogue of the
Banach self-map gate in the paper. -/
theorem scaled_ball_invariance
    (s R d dnext : Nat)
    (hd : d ≤ R)
    (hstep : 1000000000000 * dnext ≤
      1000000000000 * s + 928242792263 * d)
    (hclear : 1000000000000 * s + 928242792263 * R ≤
      1000000000000 * R) :
    dnext ≤ R := by
  omega

/-- Decreasing the perturbation radius preserves the linear part
of the scaled derivative budget. -/
theorem scaled_linear_mono (d R : Nat) (hd : d ≤ R) :
    928242792263 * d ≤ 928242792263 * R := by
  omega

#print axioms nor04_margin_exact
#print axioms nor04_margin_numerator
#print axioms scaled_ball_invariance
#print axioms scaled_linear_mono

end MathCan.InvariantBall
