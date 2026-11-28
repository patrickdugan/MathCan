import Init

/-!
# NOR-03: finite quadratic shadowing envelopes

This is the Init-only discrete recurrence component of NOR-03. It is a
kernel-checked induction over exact Nat arithmetic. Its real-analytic
application to the trained GRU uses independently established Taylor
remainder, Jacobian, and numerical-range estimates; this module does
not formalize those analytic hypotheses.

K bounds an inter-step Jacobian norm and H bounds the quadratic
Taylor forcing after clearing denominators. We use Nat for the
arithmetic certificate and preserve the exact nonlinear recurrence
instead of silently dropping the quadratic term.
-/

namespace MathCan.BlockRemainder

def radiusBound (K H r : Nat) : Nat → Nat
  | 0 => r
  | t + 1 =>
    K * radiusBound K H r t +
      H * (radiusBound K H r t * radiusBound K H r t)

def remainderBound (K H r : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 =>
    K * remainderBound K H r t +
      H * (radiusBound K H r t * radiusBound K H r t)

/-- A square is order preserving over natural numbers. -/
theorem square_mono (a b : Nat) (h : a ≤ b) :
    a * a ≤ b * b := by
  have h1 : a * a ≤ a * b := Nat.mul_le_mul_left a h
  have h2 : a * b ≤ b * b := Nat.mul_le_mul_right b h
  exact Nat.le_trans h1 h2

/-- Every nonnegative dynamics with one-step quadratic forcing
stays within the computed displacement and linearization-error envelopes. -/
theorem block_quadratic_shadowing
    (K H r : Nat) (displacement error : Nat → Nat)
    (hinitial : displacement 0 ≤ r)
    (hzero : error 0 = 0)
    (hstep : ∀ t, displacement (t + 1) ≤
      K * displacement t + H * (displacement t * displacement t))
    (herror : ∀ t, error (t + 1) ≤
      K * error t + H * (displacement t * displacement t)) :
    ∀ t,
      displacement t ≤ radiusBound K H r t ∧
      error t ≤ remainderBound K H r t := by
  intro t
  induction t with
  | zero =>
    constructor
    · simpa [radiusBound] using hinitial
    · simpa [remainderBound] using Nat.le_of_eq hzero
  | succ t ih =>
    obtain ⟨hd, he⟩ := ih
    have hsq : displacement t * displacement t ≤
        radiusBound K H r t * radiusBound K H r t :=
      square_mono _ _ hd
    have hq : H * (displacement t * displacement t) ≤
        H * (radiusBound K H r t * radiusBound K H r t) :=
      Nat.mul_le_mul_left H hsq
    have hdlin : K * displacement t ≤
        K * radiusBound K H r t :=
      Nat.mul_le_mul_left K hd
    have helin : K * error t ≤
        K * remainderBound K H r t :=
      Nat.mul_le_mul_left K he
    constructor
    · have hbound := Nat.add_le_add hdlin hq
      exact Nat.le_trans (hstep t) (by
        simpa only [radiusBound] using hbound)
    · have hbound := Nat.add_le_add helin hq
      exact Nat.le_trans (herror t) (by
        simpa only [remainderBound] using hbound)

/-- With zero initial displacement, the exact quadratic envelope
remains zero at every finite horizon. -/
theorem zero_displacement (K H t : Nat) :
    radiusBound K H 0 t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp [radiusBound, ih]

#print axioms square_mono
#print axioms block_quadratic_shadowing
#print axioms zero_displacement

end MathCan.BlockRemainder
