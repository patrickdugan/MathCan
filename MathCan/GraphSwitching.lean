import Init

/-!
NRF-02 exact cross-multiplied certificate for a two-edge path.
Denominators and vertex weights are positive in the mathematical
interpretation. No analytic Crouzeix or Banach-space result is formalized here.
-/

namespace MathCan.GraphSwitching

theorem two_edge_cross_multiply
    (w0 w1 w2 r0 r1 d0 d1 rhoNum rhoDen : Nat)
    (h0 : r0 * w0 * rhoDen ≤ d0 * rhoNum * w1)
    (h1 : r1 * w1 * rhoDen ≤ d1 * rhoNum * w2) :
    (r0 * r1) * w0 * (rhoDen * rhoDen) ≤
      (d0 * d1) * (rhoNum * rhoNum) * w2 := by
  calc
    (r0 * r1) * w0 * (rhoDen * rhoDen)
        = (r0 * w0 * rhoDen) * (r1 * rhoDen) := by ac_rfl
    _ ≤ (d0 * rhoNum * w1) * (r1 * rhoDen) :=
      Nat.mul_le_mul_right (r1 * rhoDen) h0
    _ = (d0 * rhoNum) * (r1 * w1 * rhoDen) := by ac_rfl
    _ ≤ (d0 * rhoNum) * (d1 * rhoNum * w2) :=
      Nat.mul_le_mul_left (d0 * rhoNum) h1
    _ = (d0 * d1) * (rhoNum * rhoNum) * w2 := by ac_rfl

#print axioms two_edge_cross_multiply

end MathCan.GraphSwitching
