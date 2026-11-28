import Init

/-!
# NOR-18R: exact native/cached reciprocal recurrence multiplicities

RRC25 has sixteen public candidate pairs (four U operators times four V
operators). Each unary operation appears eight times among these pairs.
One independent public check invokes the base, U and V transformations.

For each public demonstration, the unmodified sixteen-check evaluator
therefore invokes the reciprocal unary operation R exactly eight times
among U/V, plus sixteen more if the fixed public base operation is R.
A cached four-unary batch evaluates R once per demonstration.

The proof also establishes semantic equality of full-public-accepted
sets before and after exact sound prefix screening, which is the
verification parity requirement for CPU benchmarking.

CPU timing and memory measurements are external empirical evidence.
These theorems establish the arithmetic call counts, weighted
operand-width workload identities and exact filter semantics only.
-/

namespace MathCan.NOR18RReciprocalReuse

universe u
variable {Candidate : Type u}

/-- Filter the sixteen candidate programs by their full public checker. -/
def acceptedSet
    (candidates : List Candidate)
    (accepted : Candidate → Bool) : List Candidate :=
  candidates.filter accepted

/-- The complete full-check result is unchanged after a sound
    preliminary public-prefix filter. -/
theorem sound_prefix_filter_preserves_full_acceptance
    (candidates : List Candidate)
    (prefixAccepted fullAccepted : Candidate → Bool)
    (hSound : ∀ p, fullAccepted p = true → prefixAccepted p = true) :
    acceptedSet (acceptedSet candidates prefixAccepted) fullAccepted =
      acceptedSet candidates fullAccepted := by
  have hPredicate : (fun p => fullAccepted p && prefixAccepted p) =
        fullAccepted := by
    funext p
    cases hf : fullAccepted p with
    | false =>
        simp [hf]
    | true =>
        have hp : prefixAccepted p = true := hSound p hf
        simp [hf, hp]
  unfold acceptedSet
  simp only [List.filter_filter]
  rw [hPredicate]

/-- Native R invocations per demonstration: eight U/V uses, plus
    sixteen extra invocations when the fixed public base is R. -/
def nativeReciprocalCallsPerDemo (baseIsR : Bool) : Nat :=
  (if baseIsR then 16 else 0) + 8

/-- A cached 4-operator public demonstration batch calls R once. -/
def cachedReciprocalCallsPerDemo : Nat := 1

theorem reciprocal_calls_per_demo_exact_saving (baseIsR : Bool) :
    nativeReciprocalCallsPerDemo baseIsR =
      cachedReciprocalCallsPerDemo +
        (if baseIsR then 23 else 7) := by
  cases baseIsR <;>
    decide

/-- Every source's inverse recurrence has an observed integer
    bit-product workload w; recomputing it k times incurs k*w
    bit-product proxy units. The two demo sources may have different
    observed operand bit lengths. -/
def nativeReciprocalBitWork
    (baseIsR : Bool) (demo1Work demo2Work : Nat) : Nat :=
  nativeReciprocalCallsPerDemo baseIsR * (demo1Work + demo2Work)

def cachedReciprocalBitWork
    (demo1Work demo2Work : Nat) : Nat :=
  demo1Work + demo2Work

theorem exact_observed_bigint_bit_width_work_saving
    (baseIsR : Bool) (demo1Work demo2Work : Nat) :
    nativeReciprocalBitWork baseIsR demo1Work demo2Work =
      cachedReciprocalBitWork demo1Work demo2Work +
        (if baseIsR then 23 else 7) * (demo1Work + demo2Work) := by
  cases baseIsR <;>
    simp [nativeReciprocalBitWork, cachedReciprocalBitWork,
          nativeReciprocalCallsPerDemo] <;> omega

/-- A public-query reciprocal transform is common to both programs;
    adding one identical extra inverse for the query preserves the
    exact native-versus-cached demonstration-work saving. -/
theorem common_query_inverse_preserves_work_saving
    (baseIsR : Bool)
    (demo1Work demo2Work queryWork : Nat) :
    queryWork + nativeReciprocalBitWork baseIsR demo1Work demo2Work =
      queryWork + cachedReciprocalBitWork demo1Work demo2Work +
        (if baseIsR then 23 else 7) * (demo1Work + demo2Work) := by
  have h := exact_observed_bigint_bit_width_work_saving
    baseIsR demo1Work demo2Work
  omega

#print axioms sound_prefix_filter_preserves_full_acceptance
#print axioms reciprocal_calls_per_demo_exact_saving
#print axioms exact_observed_bigint_bit_width_work_saving
#print axioms common_query_inverse_preserves_work_saving

end MathCan.NOR18RReciprocalReuse
