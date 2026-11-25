# CTS-09: Dynamic LP certificate transport

Status: exact algebraic identities and synthetic development measurements. CPU only. No trained model or causal mechanism claim. No paid compute. Continues CTS-08, which established the certificate transport formula for changes in objective and right-hand side.

## Mathematical construction

For the maximization LP `max c^T x` subject to `A x <= b`, take an invertible square active-row submatrix `A_S`. Let integer `N,q` satisfy `A_S^T N = q I`, `q>0`. For fixed `A`, store the exact inverse representation and compute

    x_num = N^T b_S,
    y_num = N c,
    x = x_num/q,
    y_S = y_num/q.

Set dual coefficients off `S` to zero. The candidate is optimal if `A x_num <= q b` and `y_num >= 0`. The inverse identity establishes the active-row equalities and the dual equality. Thus `c^T x = b_S^T y_S`; weak duality proves optimality. This works for arbitrary new rational RHS and objectives (the code uses integer instances), including degeneracy if the selected basis is invertible. A cache miss is never evidence of infeasibility.

If `b=b0+B u` with fixed public `B` of size n by r, define

    x0 = N^T b0_S
    T = N^T B_S
    s0 = q b0 - A x0
    R = A T - q B.

Then `x_num=x0+T u` and exact primal feasibility is equivalent to `R u <= s0`. This replaces the online n-by-d primal matrix product with n-by-r, after preprocessing. A translation column `B_j=A v` cancels identically in `R` because `T_j=q v`. The code retains that zero column. The code also verifies the affine relation with arbitrary-precision integers before using the compressed test; an independently supplied new RHS requires direct transport unless the relation is established. Cache scope is one immutable A (and b0,B for affine entries). Changing a normal invalidates reuse unless the identity and the entire updated primal system are checked again. No certificate is accepted solely on a float score.

### Simple operation-count break-even

For one basis, the measured ledger counts n*d*(r+1) scalar product terms to precompute A*x0 and A*T; a direct primal scan uses n*d terms and a compressed scan n*r. With h tests reaching the primal scan, the affine map pays back these counted terms only if

    h > d*(r+1)/(d-r), for 0 < r < d.

This excludes the extra products needed to form T, inverse construction, factor provenance validation, memory, integer bit lengths and other costs. It is an optimistic threshold, not an end-to-end runtime theorem. For r=3 and d=8,16,32 the strict thresholds are 6.4, 4.923..., 4.414... scans, i.e. at least 7,5,5 scans per basis in this ledger. Lazy construction and removal of translation columns could improve amortization.

## Executed experiment

48 independently seeded synthetic LP sequences (four families dense/sparse/correlated/near-active; dimensions 8/16/32; structured and general RHS schedules; two roots per cell). 16d constraints including a bounding box, 16 objectives per root, 768 LPs. Four anchor objectives recur with perturbations and two fresh shocks. Both RHS and objectives change; structured RHS uses 3 public factors (one translation and two nonnegative capacity masks); general RHS uses independent random nonnegative row increments and the same translation. All LPs are feasible and bounded by construction. These are deliberately recurrent schedules, not trading or real collateral data. All instances are exposed development data.

Policies: full warm HiGHS with direct independent exact primal/dual solves; full warm HiGHS with inverse reuse but no skipped LPs; previous basis (capacity one); direct transport cache of eight; affine transport cache of eight, with direct fallback for arbitrary RHS. Multi-basis arms rank all cached entries by approximate minimum normalized dual multiplier, perform at most two exact candidate tests, then solve if needed. On a miss each policy preserves its own previous simplex basis. Least recently used eviction. Cache construction validates inverse identity using arbitrary-precision integers. Solver candidates must pass exact validation. If HiGHS cannot supply an optimal invertible basis or verification fails, the prototype aborts rather than returning an invalid result; infeasible and unbounded instances are out of scope. All timings charge solver construction, scalar RHS updates, cache construction, float ranking, exact checks, preprocessing and the shared per-policy matrix preparation; generator time excluded. HiGHS interface is private and lacks batch row-bound update in this SciPy version, so the runtime comparison is implementation-specific. No external hardware-general claim.

Integer products use NumPy int64 only when the conservative bound `width * max_abs(matrix) * max_abs(vector) <= 2^63-1` and operands fit. Otherwise use Python arbitrary-precision integers. RHS product comparison has a separate bound, and the affine precomputation uses arbitrary precision. No unsafe signed subtraction in int64. Audit covers integer overflow, cancellation and the signed minimum. Benchmark generators use small integer arithmetic; production requires exact input parsing, dimensional validation, revision binding and a fail-closed transport API.

## Results and replay

All 3,840 policy-LP outcomes accepted a valid exact certificate and agreed on objective value. Direct8 avoided 175/768 solves and used 29,165 vs 35,509 simplex iterations. Previous basis had zero hits because successive objectives intentionally switch anchors. Affine8 and direct8 had identical discrete outcomes, with 228 primal rejections after passing dual feasibility in each arm. Of 384 structured instances, 149 reused a cached basis; of 384 general instances, 26 reused a basis. Structured affine compression reduced online primal matrix product terms from 2,932,736 to 367,872, but required 7,684,096 additional precompute terms. These are counted scalar terms, not FLOPs or bit operations; affine provenance checks and other arithmetic are separately timed. No claim that lower term count implies lower runtime.

Run `summary.json` and `replay.json` are the exact source for timing and work totals. All 3,840 non-timing records matched on replay with independently permuted policy execution order. Every distinct objective/support pair was independently reconstructed with the direct rational solver and checked using arbitrary-precision products (769 pairs). 48 reversed objectives, 48 inactive-row cuts, and 48 changed active normal controls rejected or invalidated the appropriate old certificate. 384 affine-vs-direct candidate tests agree (including misses). Five overflow fixtures pass. Audit uses SymPy's same exact solver backend, but a separate explicit primal/dual/value check independent of the cached inverse and int64 path. No formal Lean kernel proof in this package.

This is a classical algorithm pilot rather than a neural causal experiment. No neural model was trained, no independent confirmation set was opened, no p-value or power-based claim is made. Prior CTS neural preflight failures remain in effect. The unit is the generated LP sequence, 48 roots with 16 related objectives each. Evidence is exact algebraic identity plus finite verified results and descriptive timings. Family-level generalization is untested. Design choices (capacity, factors, schedule, constraints, dimensions, ranking) were selected for this development run. An initial all-in-one process reached the sandbox time limit after the primary evaluation; audit and replay were subsequently completed in disjoint chunks with unchanged source. The package includes complete original result records and summary of replay, not duplicate raw replay records.

## Reproduce

    python -m pip install numpy==2.3.5 scipy==1.17.0 sympy==1.14.0
    OPENBLAS_NUM_THREADS=1 python cts09.py

If sandbox time is constrained, call `run(0,start,end)` on consecutive disjoint ranges of the 12 family/dimension strata, combine in order, `summarize`, then `audit` on disjoint root ranges and `run(1,start,end)` for replay; verify equality using `stable`. Timings will vary. `SHA256SUMS.json` records file hashes. Results are independent of the earlier trained checkpoints.

## Next

CTS-10: lazy affine maps and certified regions in factor space. Compare a cache that stores exact primal validity inequalities only after repeated use with direct transport, full warm solver and exact repeated-input memoization. Remove translation directions from residual maps and normalize exact inverse denominators before computing. Include long sequences and abrupt changes to normals, explicit infeasible/unbounded outcomes, revision identifiers, and a clearing-specific LP with row capacities and objective parameters derived from synthetic order books. Until the transport cache beats ordinary warm simplex end-to-end, prefer the full solver for general updates.
