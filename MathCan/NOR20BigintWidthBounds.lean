import MathCan.NOR19StreamedVerifier

/-!
# NOR-20: coefficient bit-width work bounds and streamed buffer scaling

NOR-20 varies four nominal integer coefficient-width tiers across four
RRC25 source families on Linux and Windows CPU runners. Exact public
verification semantics are insensitive to integer magnitudes: streaming
list equality and whole-array equality coincide for arbitrary Ints.

Bit-width resource accounting must distinguish the recorded total
operand-bitwidth-product workload from a theoretical upper bound.
If every measured operand bit length in a list of multiplication pairs
is at most B, each product has at most B^2 bit-product units; summing
over P multiplication sites yields at most P*B^2. This upper bound
does NOT assert a bound on intermediate reciprocal coefficients from
the input coefficients alone, and it is NOT a CPU runtime bound.

An idealized packed-coefficient workspace with four public unary arrays
and K materialized candidate-output arrays uses (4+K)*L*B bit slots
when each length-L coefficient is allocated an upper width B.
Streaming K=0 removes 32*L*B candidate-output bits compared to
eager caching K=32, and the saving grows monotonically with B.

The actual CPython benchmark separately measures big-integer widths,
tracemalloc peaks, timing, and host OS; those observations are not Lean
theorems.
-/

namespace MathCan.NOR20BigintWidthBounds

/-- Count exact operand-bitwidth products over a finite list of actual
    observed multiplication operand widths. -/
def observedBitProducts : List (Nat × Nat) → Nat
  | [] => 0
  | (left,right) :: tail =>
      left*right + observedBitProducts tail

/-- Conditional quadratic upper bound in the maximum *observed*
    multiplication operand width, with no uniform-input-series bound. -/
theorem observed_bitproduct_bound :
    ∀ pairs : List (Nat × Nat), ∀ width : Nat,
      (∀ p, p ∈ pairs → p.1 ≤ width ∧ p.2 ≤ width) →
        observedBitProducts pairs ≤ pairs.length * (width*width) := by
  intro pairs
  induction pairs with
  | nil =>
      intro width h
      simp [observedBitProducts]
  | cons p ps ih =>
      intro width h
      have hp : p.1 ≤ width ∧ p.2 ≤ width :=
        h p (by simp)
      have hrest : ∀ q, q ∈ ps →
          q.1 ≤ width ∧ q.2 ≤ width := by
        intro q hq
        exact h q (by simp [hq])
      have hr := ih width hrest
      have hm : p.1*p.2 ≤ width*width :=
        Nat.mul_le_mul hp.1 hp.2
      change p.1*p.2 + observedBitProducts ps ≤
          (ps.length+1)*(width*width)
      rw [Nat.add_mul]
      omega

/-- Abstract packed coefficient bit slots; source/public query buffers
    and Python object headers are outside the measured component. -/
def idealMaterializationBits
    (unaryArrays candidateArrays length maximumCoefficientBits : Nat) : Nat :=
  (unaryArrays + candidateArrays)*length*maximumCoefficientBits

theorem zero_output_streamed_packed_workspace
    (n b : Nat) :
    idealMaterializationBits 4 0 n b = 4*n*b := by
  simp [idealMaterializationBits]

/-- Exact source-width-dependent saving for 32 eager full output arrays
    relative to coefficient streaming with 4 shared unary arrays. -/
theorem packed_buffer_saving_scales_with_width
    (n b : Nat) :
    idealMaterializationBits 4 32 n b =
      idealMaterializationBits 4 0 n b + 32*n*b := by
  change (4+32)*n*b = 4*n*b + 32*n*b
  rw [Nat.add_mul, Nat.add_mul]

/-- The four-at-a-time design lies between the zero-output streamer and
    full eager two-demo caching under the same packed-slot assumption. -/
theorem four_candidate_chunk_packed_saving
    (n b : Nat) :
    idealMaterializationBits 4 32 n b =
      idealMaterializationBits 4 4 n b + 28*n*b := by
  change ((4+4)+28)*n*b = (4+4)*n*b + 28*n*b
  rw [Nat.add_mul, Nat.add_mul]

/-- A larger *actual* per-coefficient width cannot decrease the packed
    output-array saving of direct streaming. -/
theorem streaming_buffer_saving_monotone_in_width
    (length bitsSmall bitsLarge : Nat)
    (h : bitsSmall ≤ bitsLarge) :
    32*length*bitsSmall ≤ 32*length*bitsLarge := by
  exact Nat.mul_le_mul_left (32*length) h

/-- NOR-19's kernel-proven streamed equality stays exact over arbitrary
    Int coefficients, independent of size or nominal generator width. -/
theorem exact_integer_verification_all_coefficient_widths
    (candidate observed : List Int) :
    MathCan.NOR19StreamedVerifier.streamingEquals candidate observed =
      true ↔ candidate = observed := by
  exact MathCan.NOR19StreamedVerifier.streamed_exactly_iff_materialized_equal
    candidate observed

#print axioms observed_bitproduct_bound
#print axioms zero_output_streamed_packed_workspace
#print axioms packed_buffer_saving_scales_with_width
#print axioms four_candidate_chunk_packed_saving
#print axioms streaming_buffer_saving_monotone_in_width
#print axioms exact_integer_verification_all_coefficient_widths

end MathCan.NOR20BigintWidthBounds
