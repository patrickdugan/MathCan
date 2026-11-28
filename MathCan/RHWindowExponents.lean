import Init

/-!
RHD-01: dyadic window-exponent feasibility in the Alpoge/Claude RH archive.

Lean 4.35 plus Init, with no Mathlib. This tests exact integer log2
scale inequalities at two dyadic examples. They are narrower claims than
the original Real-valued SizeWindows, SizesAt and PlacesAt theorems.

Published source pin:
f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3
-/

namespace MathCan.RHWindowExponents

structure DyadicLogPoint where
  L : Nat
  den : Nat
  deltaLog : Nat
  nLog : Nat
  nTLog : Nat
  nT2Log : Nat
  mLog : Nat
  kLog : Nat
  deriving Repr

/-- Cleared-denominator log2 inequalities corresponding to the
pinned source's rank, size, depth and sample-count windows. -/
def sourceExponentChecks (w : DyadicLogPoint) : Prop :=
  52 < w.den ∧
  w.deltaLog + 32 = w.L ∧
  8 * w.den * w.L + 31 * w.L ≤ 4 * w.den * w.nLog ∧
  4 * w.den * w.nLog ≤ 8 * w.den * w.L + 33 * w.L ∧
  w.deltaLog * (2 * w.den - 1) ≤ 4 * w.den * w.mLog ∧
  4 * w.den * w.mLog ≤ w.deltaLog * (2 * w.den + 1) ∧
  18 * w.den * w.L + 39 * w.L ≤ 4 * w.den * w.kLog ∧
  4 * w.den * w.kLog ≤ 18 * w.den * w.L + 41 * w.L ∧
  8 * w.den * w.nLog ≤ 8 * w.den * w.nTLog + w.L + 8 * w.den ∧
  8 * w.den * w.nTLog + w.L ≤ 8 * w.den * w.nLog + 8 * w.den ∧
  w.den * w.nLog ≤ w.den * w.nT2Log + w.L ∧
  w.nTLog ≤ w.nLog ∧
  w.nT2Log ≤ w.nLog ∧
  w.den * w.L ≤ 2 * w.den * w.mLog + 2 * w.L ∧
  2 * w.den * w.mLog ≤ w.den * w.L + w.L ∧
  w.L + w.mLog ≤ w.kLog ∧
  2 * w.den * w.kLog + 2 * w.L ≤
    4 * w.den * w.nLog + w.den * w.L

def epsilon64 : DyadicLogPoint where
  L := 16384
  den := 64
  deltaLog := 16352
  nLog := 34816
  nTLog := 34783
  nT2Log := 34560
  mLog := 8176
  kLog := 76288

def epsilon128 : DyadicLogPoint where
  L := 32768
  den := 128
  deltaLog := 32736
  nLog := 67584
  nTLog := 67551
  nT2Log := 67328
  mLog := 16368
  kLog := 150016

theorem epsilon64_source_exponent_certificate :
    sourceExponentChecks epsilon64 := by
  unfold sourceExponentChecks epsilon64
  decide

theorem epsilon128_source_exponent_certificate :
    sourceExponentChecks epsilon128 := by
  unfold sourceExponentChecks epsilon128
  decide

/-- Logarithmic core of the necessary group-order bound from a
sampling-depth lower bound and a rank-dependent upper bound on k. -/
theorem group_log_floor_of_depth_and_k_window
    (L nLog mLog kLog : Nat)
    (hLower : L + mLog ≤ kLog)
    (hUpper : kLog ≤ 2 * nLog + mLog) :
    L ≤ 2 * nLog := by
  omega

/-- A source-family rank lower bound implies at least quadratic rank
growth on the level of binary exponents. -/
theorem quadratic_rank_of_source_family
    (L nLog margin : Nat)
    (h : 2 * L + margin ≤ nLog) :
    2 * L ≤ nLog := by
  omega

/-- The four separate SZ error contributions combine to coefficient ten.
Every bound remains an explicit premise in this independent proof. -/
theorem four_window_error_terms
    (Q a b c d : Nat)
    (h1 : a ≤ 2 * Q) (h2 : b ≤ 2 * Q)
    (h3 : c ≤ 4 * Q) (h4 : d ≤ 2 * Q) :
    a + b + c + d ≤ 10 * Q := by
  omega

/-- The additive 4X correction and 22Z principal error can be
absorbed into 26Z once X is bounded by Z. -/
theorem normalized_character_error_26
    (G X Z : Nat) (hX : X ≤ Z)
    (hG : G ≤ 4 * X + 22 * Z) :
    G ≤ 26 * Z := by
  omega

#print axioms four_window_error_terms
#print axioms normalized_character_error_26

#print axioms epsilon64_source_exponent_certificate
#print axioms epsilon128_source_exponent_certificate
#print axioms group_log_floor_of_depth_and_k_window
#print axioms quadratic_rank_of_source_family

end MathCan.RHWindowExponents
