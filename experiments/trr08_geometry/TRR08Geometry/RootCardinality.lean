module

public import TRR08Geometry.ResidueEigenvector

/-!
# Counting the actual x-coordinate fibres

Every nonidentity x-coordinate in an odd subgroup has the two points P and
-P as its fibre. Finite fibre sums give both the cardinal identity and the
change of index from nonidentity points to distinct coordinate roots.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve
open scoped BigOperators

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K}

theorem subgroupNonzero_x_fiber (H : AddSubgroup W.Point) [Fintype H]
    (Q : H) (hQ : Q ≠ 0) :
    (Finset.univ.erase (0 : H)).filter
      (fun R : H => affineX (R : W.Point) = affineX (Q : W.Point)) = {Q, -Q} := by
  classical
  ext R
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hR, hx⟩
    have hr : (R : W.Point) ≠ 0 := fun h => hR (Subtype.ext h)
    have hq : (Q : W.Point) ≠ 0 := fun h => hQ (Subtype.ext h)
    rcases (affineX_eq_iff hr hq).mp hx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact ⟨hQ, rfl⟩
    · exact ⟨neg_ne_zero.mpr hQ, by simp⟩

theorem subgroupNonzero_sum_by_roots {M : Type*} [AddCommMonoid M]
    (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) (f : K → M) :
    (∑ Q ∈ Finset.univ.erase (0 : H), f (affineX (Q : W.Point))) =
      2 • (∑ v ∈ subgroupXRoots H, f v) := by
  classical
  let s := Finset.univ.erase (0 : H)
  let x : H → K := fun Q => affineX (Q : W.Point)
  have hf := Finset.sum_fiberwise_of_maps_to' (s := s) (t := s.image x) (g := x)
    (fun Q hQ => Finset.mem_image_of_mem x hQ) f
  change (∑ Q ∈ s, f (x Q)) = 2 • (∑ v ∈ s.image x, f v)
  calc
    (∑ Q ∈ s, f (x Q)) = ∑ v ∈ s.image x, ∑ Q ∈ s with x Q = v, f v := hf.symm
    _ = ∑ v ∈ s.image x, 2 • f v := by
      apply Finset.sum_congr rfl
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨Q, hQ, rfl⟩
      have hQ0 : Q ≠ 0 := (Finset.mem_erase.mp hQ).1
      have he : s.filter (fun R => x R = x Q) = {Q, -Q} := subgroupNonzero_x_fiber H Q hQ0
      rw [he]
      simp [hno2 Q hQ0, two_nsmul]
    _ = 2 • (∑ v ∈ s.image x, f v) := Finset.smul_sum.symm

theorem subgroupXRoots_card (H : AddSubgroup W.Point) [Fintype H]
    (hno2 : ∀ Q : H, Q ≠ 0 → Q ≠ -Q) :
    2 * (subgroupXRoots H).card + 1 = Fintype.card H := by
  classical
  have h := subgroupNonzero_sum_by_roots H hno2 (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at h
  have hz : (0 : H) ∈ Finset.univ := Finset.mem_univ 0
  have hc := Finset.card_erase_add_one hz
  rw [Finset.card_univ] at hc
  omega

end TRR08Geometry

#print axioms TRR08Geometry.subgroupNonzero_x_fiber
#print axioms TRR08Geometry.subgroupNonzero_sum_by_roots
#print axioms TRR08Geometry.subgroupXRoots_card
