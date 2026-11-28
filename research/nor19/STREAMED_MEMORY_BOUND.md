# NOR-19: stream exact finite-output comparisons with bounded materialization

The NOR-18R cached public verifier gained a source-locked 4.33× median paired CPU speedup over sixteen independently recomputed native checks. Its memory measurements showed higher Python temporary allocation because it retained complete candidate output arrays during verification. NOR-19 studies exact per-coefficient comparison and a four-output chunk design while keeping the four unary transforms cached.

The new module [MathCan/NOR19StreamedVerifier.lean](../../MathCan/NOR19StreamedVerifier.lean) models a total finite-list comparator that stops on the first differing coefficient or a mismatch in list lengths. Its kernel theorem states that this streamed predicate is true **if and only if** two complete finite coefficient lists are equal. A two-demonstration corollary establishes exact acceptance parity with full list comparison.

For a public demonstration of length L, the abstract workspace accounting includes four shared unary transformation vectors. Eager full caching can retain up to 32 complete candidate-output vectors across two demonstrations. Four-at-a-time chunking retains at most four at any moment; direct coefficient streaming materializes zero full candidate-output vectors.

The workspace theorem uses a coefficient-slot model,

\[
W(L,U,K)=(U+K)L
\]

with U=4 cached unary arrays and K materialized candidate output arrays. It establishes

\[
W(L,4,32)-W(L,4,0)=32L,\quad
W(L,4,32)-W(L,4,4)=28L.
\]

These identities certify the **algorithmic buffer count**, not a bound on all memory allocated by a Python implementation. They exclude the public query prediction arrays, temporary bigint values, object headers, garbage collector state, preexisting public inputs, and host-level memory mappings. The companion NOR-19 benchmark measures the complete Python-traced peak in separate untimed passes, as well as verification-only peak and process RSS.

The NOR-19 public fixture contains 64 previously unbenchmarked NOR-18 test sources from four original cohorts, selected by fixed indices and accompanied by immutable source hashes. The five algorithm implementations must reproduce all original NOR-18 exact acceptance masks and future-output unanimity certificates, without reading planted program identities or withheld query targets. The primary test is the streamed verify-first implementation; success needs at least a 20% median peak Python allocation reduction versus original cached verification, improvement on 48 of 64 individual sources, and at least 2× paired complete CPU speedup over native independent verification.

The mathematical results establish exact acceptance semantics and abstract materialization bounds. Actual memory reduction and CPU speed preservation depend on source-specific hosted measurements and the registered benchmark.
