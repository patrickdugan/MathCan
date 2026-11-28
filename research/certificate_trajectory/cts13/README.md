# CTS-13: exact scalar certificate contraction

Status: elementary algebraic identity, exact finite audits, exposed synthetic development benchmark. No neural claim, production deployment or independent confirmation.

## Contract

For fixed A,b0,B and invertible A_S, write A_S^T N=qI, q>0. Precompile x0=N^T b0_S, T=N^T B_S; x_num=x0+Tu. The exact primal and dual tests are (AT-qB)u <= q b0-A x0 and Nc>=0. By weak duality this certifies the optimum. A translation column B_j=A v can be omitted from the primal scan, and its vertex-map column is qv. For an objective c, the numerator of the value equals alpha+beta^T u, alpha=c^T x0, beta=T^T c. Cache the coefficients under the full canonical int64 objective bytes, within a basis and revision. Use Python arbitrary-precision integer dots for coefficient construction and scalar evaluation. The RHS and objective envelope is checked by the existing exact API. Four objective coefficient records per basis, LRU eviction. Coefficients are computed only after passing the exact feasibility checks. Value-only receipts bind the current snapshot, objective bytes, revision, basis and value, and are accepted for settlement only by object identity. Reconstruct x_num when requested; subsequent requests may reuse the vertex for that receipt. Replacing the snapshot or receipt invalidates the old one. Internal quote() assumes the trusted solver has verified its result; this is not a general-purpose attestation or authorization interface.

## Amortization identity

Ignoring common work, with d variables and r factor columns, reconstructing a vertex and then contracting with c costs d(r+1) scalar product terms per quote (the translation column is already precompiled). For h quotes under the same retained objective key, with k of them requiring full allocation, the memoized path counts d(r+1)+hr+krd. Memoization saves counted products exactly when h[d(r+1)-r] > d(r+1)+krd. For k=h, the inequality becomes h(d-r)>d(r+1); for k=0 the threshold is lower. This is a principal-product ledger, not wall-clock time, bit complexity or a bound on the full solver. Cold coefficients without memoization cost d(r+1)+r per quote even before allocation, so algebraic contraction alone need not save arithmetic.

## Protocol

24 fresh synthetic roots, 64 updates each, seeds 38013+100000*family+1000*d+100*mode. Four families (dense, sparse, correlated, near), d in {8,16,32}, recurring and mixed raw/structured regimes. Cache 8 bases, 2 candidates ranked by float cone score, exact acceptance and identical fallback warm HiGHS. 16 randomly selected settlement requests per root shared across full_reuse, vertex, scalar and memo. memo_all requests every allocation (stress arm with a different output requirement, not a fair runtime comparison). Two randomized arm orderings. Full reuse baseline includes exact reconstruction and verification. Fixture RHS reconstruction after timing is excluded from policy time. No GPU or paid compute.

| Arm | Calls | Iterations | Run 1 s | Run 2 s |
| --- | ---: | ---: | ---: | ---: |
| Full warm HiGHS + inverse reuse | 1536 | 70883 | 9.6663 | 9.7849 |
| Vertex reconstruction | 742 | 36823 | 7.9716 | 8.0519 |
| Scalar contraction | 742 | 36823 | 7.9857 | 8.0693 |
| Memoized contraction | 742 | 36823 | 8.0285 | 8.1325 |
| Memoized, all allocations | 742 | 36823 | 7.9872 | 8.1207 |

All 7680 outcomes agree on exact objective values. Cache arms share bases, hits, LP calls and iterations. Memo has 385 hits, 84 misses, 0 evictions on the main workload. Of 469 eligible quotes, 122 require deferred reconstruction, 347 avoid it. 384 requested allocations per comparable arm, 1536 for memo_all. Vertex, scalar, memo and memo_all count 948648, 956535, 929911, 947407 combined vertex, objective and coefficient product terms respectively (includes direct checks, excludes shared primal scans, inverse/affine compilation and other work). For the accepted compiled quotes alone the corresponding products are 31968, 39855, 13231, 30727. Memo reduces this subset by 58.61%, but only 1.98% of the wider ledger. Timing is descriptive: memo is 16.89–16.94% faster than full solver with inverse reuse, 0.71–1.00% slower than the vertex baseline. Full reconstruction stress is not directly comparable due to serialization and different allocation volume. No runtime improvement attributable to scalar memoization established.

## Audits

7680/7680 replay rows agree outside timings. Independently solved 1536 distinct snapshot/support pairs and checked exact primal/dual equality, nonnegative dual multipliers and objective agreement. 1152 factor scalar identities verified; 3072 returned allocations agree with independent rational solves. 24 each stale snapshot, fabricated receipt, foreign receipt, wrong objective, changed revision and raw invalidating cut controls rejected. 24 distinct objective keys agree with the vertex contraction. Large product fixture 3*2^80 passes. Additional 11-objective fixture validates five LRU evictions, two hits and ten replaced receipt rejections. This tests a trusted serial interface; hostile access, cryptographic attestations, parallel clearing and real market data are untested.

## Reproduction

Python 3.13-compatible, NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0 (actual environment Python version recorded below). From the experiment directory: `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python reproduce.py`. On MathCan use `PYTHONPATH=../cts12:../cts11` when the original dependencies live in those directories. Replay regenerates non-timing outcomes; timing varies. Audit output, compact receipt and SHA256 manifest provide source provenance. Larger raw trajectories remain in the package. No new Lean verification.

## Next gate (CTS-14)

Cache exact dual multipliers under the same objective key, rather than recomputing Nc on every repeated objective. A dual sign bit alone is insufficient unless its provenance binds the inverse, objective and revision. Keep primal feasibility checks and deferred allocations intact; compare the cost of reuse and invalidation on recurring and high-churn objectives. Add an explicit finite memory budget and a no-repeat negative control.

Executed environment: Python 3.13.5.
