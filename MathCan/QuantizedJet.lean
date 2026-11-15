import Init

/-!
Exact integer coordinates for a quantized jet recurrence. A physical unit is
1/(2*D). The encoder uses the true residual and the previous decoder error;
the decoder itself only uses the transmitted integer correction. No floating
point arithmetic, choice of a rounding oracle, or smallness of t is assumed.
-/
namespace MathCan.QuantizedJet

def nearest (D a : Int) : Int := (a + D) / (2 * D)

/-- The half-open tie convention yields a closed half-unit error bound. -/
theorem nearest_residual (D a : Int) (hD : 0 < D) :
    -D ≤ (2 * D) * nearest D a - a ∧
    (2 * D) * nearest D a - a ≤ D := by
  have hp : 0 < 2 * D := by omega
  have h0 := Int.emod_nonneg (a + D) (by omega : 2 * D ≠ 0)
  have h1 := Int.emod_lt_of_pos (a + D) hp
  have he := Int.emod_add_mul_ediv (a + D) (2 * D)
  simp only [nearest, Int.mul_comm] at *
  omega

/-- The corrected sign cancels the transported previous error. -/
theorem corrected_error_identity (D t u v r c : Int) :
    (t * v + (2 * D) * c) - (t * u + r) =
      (2 * D) * c - (r - t * (v - u)) := by
  simp only [Int.mul_sub]
  omega

/-- One step has error at most half a quantization unit, for any transport. -/
theorem corrected_step_stable (D t u v r : Int) (hD : 0 < D) :
    let c := nearest D (r - t * (v - u));
    -D ≤ (t * v + (2 * D) * c) - (t * u + r) ∧
    (t * v + (2 * D) * c) - (t * u + r) ≤ D := by
  dsimp
  rw [corrected_error_identity]
  exact nearest_residual D _ hD

/-- A bounded transported error and true residual give a bounded alphabet.
    All bounds are in the same exact integer coordinate scale. -/
theorem correction_alphabet_bound (D a r z R E : Int) (hD : 0 < D)
    (ha : a = r - z) (hr : -R ≤ r ∧ r ≤ R)
    (hz : -E ≤ z ∧ z ≤ E) :
    -(R + E + D) ≤ (2 * D) * nearest D a ∧
    (2 * D) * nearest D a ≤ R + E + D := by
  have h := nearest_residual D a hD
  omega

/-- Uniform stream stability; the bound does not grow with the time index. -/
theorem corrected_stream_stable
    (D : Int) (hD : 0 < D) (t r u v : Nat → Int)
    (hu : ∀ i, u (i + 1) = t i * u i + r i)
    (hv : ∀ i, v (i + 1) = t i * v i +
      (2 * D) * nearest D (r i - t i * (v i - u i)))
    (h0 : -D ≤ v 0 - u 0 ∧ v 0 - u 0 ≤ D) :
    ∀ i, -D ≤ v i - u i ∧ v i - u i ≤ D := by
  intro i
  cases i with
  | zero => exact h0
  | succ i =>
      rw [hu i, hv i]
      exact corrected_step_stable D (t i) (u i) (v i) (r i) hD

/-- The same exact reset works coordinatewise for any finite-dimensional
    predictor. This does not assert a matrix norm estimate. -/
theorem vector_predictor_stable {n : Nat} (D : Int) (hD : 0 < D)
    (target prediction : Fin n → Int) :
    ∀ j, -D ≤ (prediction j + (2 * D) *
      nearest D (target j - prediction j)) - target j ∧
      (prediction j + (2 * D) *
      nearest D (target j - prediction j)) - target j ≤ D := by
  intro j
  have h := nearest_residual D (target j - prediction j) hD
  omega

#print nearest_residual
#print corrected_error_identity
#print corrected_step_stable
#print correction_alphabet_bound
#print corrected_stream_stable
#print vector_predictor_stable
#print axioms nearest_residual
#print axioms corrected_error_identity
#print axioms corrected_step_stable
#print axioms correction_alphabet_bound
#print axioms corrected_stream_stable
#print axioms vector_predictor_stable

end MathCan.QuantizedJet
