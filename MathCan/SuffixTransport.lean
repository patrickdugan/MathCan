import Init

/-!
NRF-08: the off-diagonal block of a composite tangent map.
This Init-only Nat theorem formalizes the block multiplication skeleton.
The real-matrix Frobenius norm bounds are written and independently
checked by an exact-rational oracle, not formalized here.
-/

namespace MathCan.SuffixTransport

structure Block2 where
  vv : Nat
  vd : Nat
  dv : Nat
  dd : Nat

def blockMul (s j : Block2) : Block2 :=
  ⟨s.vv * j.vv + s.vd * j.dv,
   s.vv * j.vd + s.vd * j.dd,
   s.dv * j.vv + s.dd * j.dv,
   s.dv * j.vd + s.dd * j.dd⟩

/-- The visible-dark channel is the transported old channel plus injection. -/
theorem visibleDark_transport (s j : Block2) :
    (blockMul s j).vd = s.vv * j.vd + s.vd * j.dd := by
  rfl

def shear (b : Nat) : Block2 := ⟨1, b, 0, 1⟩

/-- In a unipotent shear, the two source contributions add. -/
theorem shear_transport (b c : Nat) :
    (blockMul (shear b) (shear c)).vd = b + c := by
  simp [blockMul, shear, Nat.add_comm]

#print axioms visibleDark_transport
#print axioms shear_transport

end MathCan.SuffixTransport
