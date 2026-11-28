import Init

/-!
NOR-09: asynchronous two-source, two-basin late-history stitching.

Two separately sourced recurrent trajectories enter distinct certified
invariant balls after different finite capture times. A finite-window
embedding of their observed states and two attractor anchors can then
be extended to all later block-sampled times by clipping each stream
to its own anchor. The exact metric distortion bound is independent
of differences between the two source capture times.

The real-valued Banach and finite Lp dimension reduction arguments
are written in research/nor09/ASYNCHRONOUS_TWO_ANCHOR.md. This file
kernel-checks their Nat-metric stitching and capture-clock core.
-/

namespace MathCan.NOR09Asynchronous

/-- Bounds both directions of the distance change when two true states
are replaced by separate basin anchors. No common capture clock is used. -/
theorem cross_anchor_distance
    {State : Type} (d : State → State → Nat)
    (triangle : ∀ u v w, d u w ≤ d u v + d v w)
    (symmetric : ∀ u v, d u v = d v u)
    (x y anchorX anchorY : State)
    (rX rY : Nat)
    (hx : d x anchorX ≤ rX)
    (hy : d y anchorY ≤ rY) :
    d x y ≤ d anchorX anchorY + rX + rY ∧
    d anchorX anchorY ≤ d x y + rX + rY := by
  have hBackX : d anchorX x ≤ rX := by
    rw [symmetric anchorX x]
    exact hx
  have hBackY : d anchorY y ≤ rY := by
    rw [symmetric anchorY y]
    exact hy
  have h1 := triangle x anchorX anchorY
  have h2 := triangle x anchorY y
  have h3 := triangle anchorX x y
  have h4 := triangle anchorX y anchorY
  constructor <;> omega

/-- Measured finite-anchor embedding error E and two late tail radii
produce an all-late additive metric error E+rX+rY. -/
theorem encoded_cross_anchor_error
    {State : Type} (d : State → State → Nat)
    (triangle : ∀ u v w, d u w ≤ d u v + d v w)
    (symmetric : ∀ u v, d u v = d v u)
    (x y anchorX anchorY : State)
    (encodedAnchorGap E rX rY : Nat)
    (hAnchor : d anchorX anchorY ≤ encodedAnchorGap + E ∧
               encodedAnchorGap ≤ d anchorX anchorY + E)
    (hx : d x anchorX ≤ rX) (hy : d y anchorY ≤ rY) :
    d x y ≤ encodedAnchorGap + (E + rX + rY) ∧
    encodedAnchorGap ≤ d x y + (E + rX + rY) := by
  obtain ⟨hTrue, hReverse⟩ :=
    cross_anchor_distance d triangle symmetric
      x y anchorX anchorY rX rY hx hy
  obtain ⟨hE, hR⟩ := hAnchor
  constructor <;> omega

/-- Clipping two states of the same basin to one common anchor incurs
at most the sum of their separate true-state tail radii. -/
theorem same_anchor_late_pair
    {State : Type} (d : State → State → Nat)
    (triangle : ∀ u v w, d u w ≤ d u v + d v w)
    (symmetric : ∀ u v, d u v = d v u)
    (x y anchor : State) (rX rY : Nat)
    (hx : d x anchor ≤ rX)
    (hy : d y anchor ≤ rY) :
    d x y ≤ rX + rY := by
  have hBack : d anchor y ≤ rY := by
    rw [symmetric anchor y]
    exact hy
  have htri := triangle x anchor y
  omega

/-- The two source capture times are independent. Once their time-
indexed tail estimates hold, every cross-stream late pair is controlled
by the corresponding distinct attractor anchors. -/
theorem asynchronous_capture_clipping
    {State : Type} (d : State → State → Nat)
    (triangle : ∀ u v w, d u w ≤ d u v + d v w)
    (symmetric : ∀ u v, d u v = d v u)
    (streamX streamY : Nat → State)
    (anchorX anchorY : State)
    (captureX captureY rX rY : Nat)
    (lateX : ∀ t, captureX ≤ t → d (streamX t) anchorX ≤ rX)
    (lateY : ∀ t, captureY ≤ t → d (streamY t) anchorY ≤ rY) :
    ∀ i j, captureX ≤ i → captureY ≤ j →
      d (streamX i) (streamY j) ≤
          d anchorX anchorY + rX + rY ∧
      d anchorX anchorY ≤
          d (streamX i) (streamY j) + rX + rY := by
  intro i j hi hj
  exact cross_anchor_distance d triangle symmetric
    (streamX i) (streamY j) anchorX anchorY
    rX rY (lateX i hi) (lateY j hj)

/-- A single common terminal code with zero decoded distance cannot
preserve two separated late streams below their cross-basin margin. -/
theorem distinct_terminal_codes_required
    (anchorGap truePairDistance rX rY allowedError : Nat)
    (hTrue : anchorGap ≤ truePairDistance + rX + rY)
    (hCollision : truePairDistance ≤ allowedError)
    (hSeparated : rX + rY + allowedError < anchorGap) : False := by
  omega

#print axioms cross_anchor_distance
#print axioms encoded_cross_anchor_error
#print axioms same_anchor_late_pair
#print axioms asynchronous_capture_clipping
#print axioms distinct_terminal_codes_required

end MathCan.NOR09Asynchronous
