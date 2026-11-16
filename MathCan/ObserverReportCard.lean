import Init

/-!
# ROC-01: finite observer counterexamples and quotient propagation

These kernel-checked statements are narrower than Part 2's real-matrix
observability singular-value bound. They certify a rank-one code for four
Boolean states, a dynamic dark-to-observed witness, and all-depth propagation
of an assumed fiber-compatibility condition.

The real rotation's no-rank-two-extension statement and the Frobenius/Gram
lower bound remain written proofs with exact-rational regression tests.
-/

namespace MathCan.ObserverReportCard

/-- A single rational/integer scalar observer encodes four distinct states. -/
def bitPairCode (x y : Bool) : Nat :=
  (if x then 1 else 0) + 2 * (if y then 1 else 0)

theorem bitPairCode_injective
    (a b c d : Bool)
    (h : bitPairCode a b = bitPairCode c d) :
    a = c ∧ b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [bitPairCode] at h ⊢

/-- A state with a hidden second coordinate may write it into the visible first one. -/
def outputRegister (v : Int × Int) : Int × Int := (v.1 + v.2, v.2)
def readFirst (v : Int × Int) : Int := v.1

theorem outputRegister_currently_hidden :
    readFirst (0, 1) = readFirst (0, 0) := by
  rfl

theorem outputRegister_next_step_visible :
    readFirst (outputRegister (0, 1)) ≠
    readFirst (outputRegister (0, 0)) := by
  decide

/-- A 2D rotation in the last two coordinates, with an independent visible register. -/
def rotation3 (s : Int × (Int × Int)) : Int × (Int × Int) :=
  (s.1, (-s.2.2, s.2.1))
def readOne (s : Int × (Int × Int)) : Int := s.1
def readTwo (s : Int × (Int × Int)) : Int × Int :=
  (s.1, s.2.1)

theorem rotation3_rank_one_readout_closed (s : Int × (Int × Int)) :
    readOne (rotation3 s) = readOne s := by
  rfl

theorem rotation3_two_coordinate_readout_not_closed :
    readTwo (0, (0, 1)) = readTwo (0, (0, 0)) ∧
    readTwo (rotation3 (0, (0, 1))) ≠
      readTwo (rotation3 (0, (0, 0))) := by
  decide

/-- Iterate the same state update with no assumption of contraction. -/
def iterate {S : Type} (f : S → S) : Nat → S → S
  | 0, x => x
  | n + 1, x => f (iterate f n x)

/-- Any exact one-step observable quotient respects every subsequent depth. -/
theorem fiber_compatible_all_depths
    {S V : Type} (f : S → S) (q : S → V)
    (hc : ∀ a b, q a = q b → q (f a) = q (f b))
    (n : Nat) (a b : S) (hab : q a = q b) :
    q (iterate f n a) = q (iterate f n b) := by
  induction n with
  | zero =>
      simpa [iterate] using hab
  | succ n ih =>
      simpa [iterate] using hc (iterate f n a) (iterate f n b) ih

#print axioms bitPairCode_injective
#print axioms outputRegister_next_step_visible
#print axioms rotation3_rank_one_readout_closed
#print axioms rotation3_two_coordinate_readout_not_closed
#print axioms fiber_compatible_all_depths

end MathCan.ObserverReportCard
