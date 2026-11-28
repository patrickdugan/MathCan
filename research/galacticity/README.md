# GAL-01: resource-accounted finite scale

Companion implementation: https://github.com/MoralityLabAI/Compactification-Theory/tree/research/gal01-nonperturbative-20261128/Galacticity

The Lean module MathCan/Galacticity.lean contains arithmetic and indistinguishability
lemmas, with no sorry or new axioms. It is a candidate formalization: the
Lean toolchain is not available in the authoring environment, and no successful
kernel replay is asserted. Run lake env lean MathCan/Galacticity.lean using
the repository-pinned toolchain. No import into the existing root module
until that gate passes.

## Semantic theorem (paper proof)

Let K,b,m be positive integers. The hidden input is an arbitrary matrix of
K rows and b bits per row. A deterministic online exact machine sees row
addresses, probes any individual input bit, can keep arbitrary state, and
returns one parity bit for each address. The cost is the count of probes
from cold start (including setup) plus m returned answers. All other
operations are free; storage sufficient to memoize row parity is allowed.
The machine receives no instance-dependent uncharged advice.

For every fixed legal sequence of distinct row addresses (until exhaustion),
and every input x, suppose a requested row has a bit j still unread when
its answer is emitted. Construct y by flipping j alone. All probes on the
path up to that output return the same answers as on x, by induction on
the deterministic sequence of actions, and all revealed addresses coincide.
The output is unchanged, but parity differs. This violates exactness.
Thus every distinct requested row costs b probes at minimum. A sequence
with min(K,m) distinct rows witnesses the worst-case lower bound. Lazy
memoization probes all b bits exactly once per distinct row and emits m
answers. The exact optimum is b min(K,m)+m.

For a factor q>1, the scan baseline m(b+1) equals the optimum for m<=K.
For m>=K, q-fold gain requires m(b+1-q)>=qKb. If q>=b+1 this is
impossible; otherwise the threshold is ceil(qKb/(b+1-q)), which is strictly
above K. If K=2^k the address-width threshold grows exponentially in k
(and linearly in the database size). All bounds are relative to the
explicit bit-probe model, cost convention and scan baseline.

If preprocessing is allowed p probes but each possible first query is
limited to t<b additional probes, then every preprocessing transcript must
leave at most t unread bits in every row, since any row can be chosen.
Thus p>=K(b-t) on every preprocessing path. Precompute one partial parity
per row to match the probe bound; account for its storage separately.

## Formal boundary
The Lean candidate proves the algebra of the cost envelope, prefix and
ceiling obstruction, monotonicity and a local indistinguishability lemma.
The full adaptive machine transcript induction, construction correctness,
integer ceiling minimality, randomized and succinct-input extensions are
not kernel-formalized. The next proof target is a trace semantics with
adaptive reads and a theorem connecting transcript equality to parity
of an arbitrary unqueried coordinate.

## Novelty boundary
This is an elementary adversarial data-access result. Literature on
cell-probe and preprocessing tradeoffs already addresses related phenomena.
It is a test case for the proposed finite-scale profile, not a claim of
an unrestricted complexity-theoretic breakthrough.
