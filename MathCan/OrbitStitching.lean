import Init

/-!
# NOR-01: exact finite-window/tail stitching

This module kernel-checks a discrete, quantitative lemma. A symmetric
integer-valued metric with bounded late points can be approximated at all
horizons by zero-clipping a finite-window sketch. The general complex
numerical-range inequality and Lp dimension reduction are imported at paper
level in the accompanying research note; this file does not formalize them.

Index 0 is a distinguished zero anchor. Indices 1..cutoff are observed
orbit states, and indices above cutoff are clipped to the anchor.
-/
namespace MathCan.OrbitStitching

/-- A pair of tail points, each within `radius` of anchor 0, have
mutual distance at most twice that radius. -/
theorem two_tail_radius
    (cutoff radius : Nat) (d : Nat → Nat → Nat)
    (triangle : ∀ i j k, d i k ≤ d i j + d j k)
    (symmetric : ∀ i j, d i j = d j i)
    (tail : ∀ i, cutoff < i → d 0 i ≤ radius)
    (i j : Nat) (hi : cutoff < i) (hj : cutoff < j) :
    d i j ≤ 2 * radius := by
  have h1 : d 0 i ≤ radius := tail i hi
  have h2 : d 0 j ≤ radius := tail j hj
  have h3 : d i 0 ≤ radius := by
    rw [symmetric i 0]
    exact h1
  have h4 := triangle i 0 j
  omega

/-- Finite-window additive error `E` and late-orbit radius `B`
combine into all-horizon additive error at most `E + 2 B`.
The clipped sketch distance equals anchor distance in a cross pair,
and vanishes if both points are in the tail. -/
theorem additive_tail_stitch
    (cutoff windowError tailRadius : Nat)
    (original sketched : Nat → Nat → Nat)
    (triangle : ∀ i j k, original i k ≤ original i j + original j k)
    (symmetric : ∀ i j, original i j = original j i)
    (window : ∀ i j, i ≤ cutoff → j ≤ cutoff →
      original i j ≤ sketched i j + windowError ∧
      sketched i j ≤ original i j + windowError)
    (tail : ∀ i, cutoff < i → original 0 i ≤ tailRadius)
    (crossLeft : ∀ i j, i ≤ cutoff → cutoff < j →
      sketched i j = sketched i 0)
    (crossRight : ∀ i j, cutoff < i → j ≤ cutoff →
      sketched i j = sketched 0 j)
    (late : ∀ i j, cutoff < i → cutoff < j →
      sketched i j = 0) :
    ∀ i j,
      original i j ≤ sketched i j + windowError + 2 * tailRadius ∧
      sketched i j ≤ original i j + windowError + 2 * tailRadius := by
  intro i j
  by_cases hi : i ≤ cutoff
  · by_cases hj : j ≤ cutoff
    · obtain ⟨h1, h2⟩ := window i j hi hj
      constructor <;> omega
    · have hj' : cutoff < j := by omega
      have h0j := tail j hj'
      have hj0 : original j 0 ≤ tailRadius := by
        rw [symmetric j 0]
        exact h0j
      have ⟨hwin1, hwin2⟩ := window i 0 hi (Nat.zero_le cutoff)
      have ht1 := triangle i 0 j
      have ht2 := triangle i j 0
      have hs := crossLeft i j hi hj'
      constructor <;> omega
  · have hi' : cutoff < i := by omega
    by_cases hj : j ≤ cutoff
    · have h0i := tail i hi'
      have hi0 : original i 0 ≤ tailRadius := by
        rw [symmetric i 0]
        exact h0i
      have ⟨hwin1, hwin2⟩ := window 0 j (Nat.zero_le cutoff) hj
      have ht1 := triangle i 0 j
      have ht2 := triangle 0 i j
      have hs := crossRight i j hi' hj
      constructor <;> omega
    · have hj' : cutoff < j := by omega
      have hd := two_tail_radius cutoff tailRadius original triangle symmetric
        tail i j hi' hj'
      have hs := late i j hi' hj'
      constructor <;> omega

#print axioms two_tail_radius
#print axioms additive_tail_stitch

end MathCan.OrbitStitching
