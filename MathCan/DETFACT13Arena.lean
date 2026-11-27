import Lean

/-! Abstract byte layout for the fixed arena. C pointer operations,
Montgomery arithmetic, allocator and compiler are outside this model. -/
namespace MathCan.DETFACT13Arena

def words (L E b : Nat) : Nat := (b + 8) * L + E + 2

def bytes (L E b r c : Nat) : Nat := 4 * words L E b + r + 1 + c

def Fits (L E b r c cap : Nat) : Prop := bytes L E b r c ≤ cap

theorem words_match_layout (L E b : Nat) :
    6 * L + (2 * L + 2) + b * L + E = words L E b := by
  unfold words
  rw [Nat.add_mul]
  omega

/-- Conditional on an index lying in the assigned slice. -/
theorem slice_access_bounded (offset width index total : Nat)
    (hSlice : offset + width ≤ total) (hIndex : index < width) :
    offset + index < total := by omega

theorem multi_byte_access_bounded (offset width index length total : Nat)
    (hSlice : offset + width ≤ total) (hAccess : index + length ≤ width) :
    offset + index + length ≤ total := by omega

theorem adjacent_disjoint (offset width i j : Nat)
    (hi : i < width) : offset + i < offset + width + j := by omega

theorem endpoints (L E b r c : Nat) :
    4 * (6 * L) ≤ bytes L E b r c ∧
    4 * (6 * L + (2 * L + 2)) ≤ bytes L E b r c ∧
    4 * (6 * L + (2 * L + 2) + b * L) ≤ bytes L E b r c ∧
    4 * (6 * L + (2 * L + 2) + b * L + E) + (r + 1) + c =
      bytes L E b r c := by
  unfold bytes
  rw [← words_match_layout L E b]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem bytes_monotone_slots (L E b r c₁ c₂ : Nat) (h : c₁ ≤ c₂) :
    bytes L E b r c₁ ≤ bytes L E b r c₂ := by
  unfold bytes
  omega

/-- A minimum available segment size is feasible iff some grid member is. -/
theorem minimum_complete (L E b r cap c₀ : Nat) (slots : List Nat)
    (hmem : c₀ ∈ slots) (hmin : ∀ c, c ∈ slots → c₀ ≤ c) :
    Fits L E b r c₀ cap ↔ ∃ c, c ∈ slots ∧ Fits L E b r c cap := by
  constructor
  · intro h
    exact ⟨c₀, hmem, h⟩
  · intro h
    obtain ⟨c, hc, hf⟩ := h
    exact Nat.le_trans (bytes_monotone_slots L E b r c₀ c (hmin c hc)) hf

/-- Input-domain bounds are premises, not a verification of the parser. -/
theorem domain_arena_bound (L E b r c : Nat)
    (hL : L ≤ 128) (hE : E ≤ 128) (hb : b ≤ 128)
    (hr : r ≤ 3162) (hc : c ≤ 4999999) :
    bytes L E b r c ≤ 5073314 := by
  have hm : (b + 8) * L ≤ 136 * 128 := Nat.mul_le_mul (by omega) hL
  unfold bytes words
  omega

theorem multiply_add_fits_u64 (a b c d : Nat)
    (ha : a < 4294967296) (hb : b < 4294967296)
    (hc : c < 4294967296) (hd : d < 4294967296) :
    a * b + c + d < 18446744073709551616 := by
  have hm : a * b ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

#print axioms words_match_layout
#print axioms endpoints
#print axioms minimum_complete
#print axioms domain_arena_bound
#print axioms multiply_add_fits_u64
end MathCan.DETFACT13Arena
