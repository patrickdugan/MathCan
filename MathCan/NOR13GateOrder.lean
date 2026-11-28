import Init

/-!
# NOR-13R: gate-endpoint ordering and mode-code identifiability

For a frozen task head with scores affine in one gate coordinate g,
s_j(g) = a_j + g b_j, g in [-1,1], every pairwise score gap is
affine in g. If the candidate order agrees at g=-1 and g=+1,
it agrees throughout the closed interval.

The executable companion checks this endpoint condition using exact
binary-rational lifts of the frozen trained float coefficients.
Here the discrete positive-weight core is verified with the Lean
kernel, over Nat-valued endpoint scores. This supports every rational
gate g=-1+2t/N with 0 <= t <= N. The analytic real interpolation
and deterministic sorting transfer are documented separately.

A gate can be highly predictive of an attractor while irrelevant to
ranking when these endpoint comparisons remain invariant.
-/
namespace MathCan.NOR13GateOrder

/-- Unnormalized convex interpolation between endpoint scores.
    For t<=N, weights N-t and t are nonnegative. -/
def weightedEndpoints (N t first last : Nat) : Nat :=
  (N-t)*first + t*last

/-- Pairwise order at both endpoints implies order for every
    nonnegative choice of endpoint weights. -/
theorem endpoint_order_conserves_weighted_order
    (firstA firstB lastA lastB lo hi : Nat)
    (hFirst : firstA <= firstB)
    (hLast : lastA <= lastB) :
    lo*firstA + hi*lastA <= lo*firstB + hi*lastB := by
  exact Nat.add_le_add
    (Nat.mul_le_mul_left lo hFirst)
    (Nat.mul_le_mul_left hi hLast)

/-- In particular, the order is preserved at every finite gate
    interpolation step t=0,...,N. -/
theorem endpoints_certify_every_finite_gate
    (N t firstA firstB lastA lastB : Nat)
    (hFirst : firstA <= firstB)
    (hLast : lastA <= lastB) :
    weightedEndpoints N t firstA lastA <=
      weightedEndpoints N t firstB lastB := by
  unfold weightedEndpoints
  exact endpoint_order_conserves_weighted_order
    firstA firstB lastA lastB (N-t) t hFirst hLast

/-- The same theorem applies simultaneously to every ordered pair
    of candidates in a finite or infinite index set. -/
theorem all_candidate_pairs_preserve_order
    {Index : Type}
    (N t : Nat) (lower upper : Index -> Nat)
    (h : forall i j, lower i <= lower j -> upper i <= upper j) :
    forall i j, lower i <= lower j ->
      weightedEndpoints N t (lower i) (upper i) <=
      weightedEndpoints N t (lower j) (upper j) := by
  intro i j hij
  exact endpoints_certify_every_finite_gate
    N t (lower i) (lower j) (upper i) (upper j)
    hij (h i j hij)

/-- Fixed one-versus-many top-score witness. Its candidate is ranked
    at least as high as all competitors at any gate interpolation step. -/
theorem top_candidate_from_two_endpoints
    {Index : Type}
    (N t : Nat) (lower upper : Index -> Nat) (winner : Index)
    (hLo : forall j, lower j <= lower winner)
    (hHi : forall j, upper j <= upper winner) :
    forall j,
      weightedEndpoints N t (lower j) (upper j) <=
      weightedEndpoints N t (lower winner) (upper winner) := by
  intro j
  exact endpoints_certify_every_finite_gate
    N t (lower j) (lower winner) (upper j) (upper winner)
    (hLo j) (hHi j)

/-- The strict endpoint lead survives with positive weight even if
    the other endpoint ties. This handles a typical deterministic
    candidate-order tie-break margin certificate. -/
theorem strict_pair_at_one_endpoint
    (firstA firstB lastA lastB lo hi : Nat)
    (hFirst : firstA < firstB)
    (hLast : lastA <= lastB)
    (hLo : lo > 0) :
    lo*firstA + hi*lastA < lo*firstB + hi*lastB := by
  have hstrict : lo*firstA < lo*firstB :=
    Nat.mul_lt_mul_of_pos_left hFirst hLo
  have hweak : hi*lastA <= hi*lastB :=
    Nat.mul_le_mul_left hi hLast
  omega

#print axioms endpoint_order_conserves_weighted_order
#print axioms endpoints_certify_every_finite_gate
#print axioms all_candidate_pairs_preserve_order
#print axioms top_candidate_from_two_endpoints
#print axioms strict_pair_at_one_endpoint

end MathCan.NOR13GateOrder
