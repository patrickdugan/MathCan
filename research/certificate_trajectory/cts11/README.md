# CTS-11: revision-bound exact factor updates

**Evidence status:** algebraic identity, exact finite audit and synthetic development benchmark. Classical code only. No paid compute or model training. Continues CTS-10 using new generator seeds (38011 series).

## Mathematical contract

Fix a revision consisting of integer A, b0, B and translation vector v, with B[:,0]=A v. The update service constructs b=b0+B u exactly. For active rows S, let A_S^T N=q I with q>0. Put x_num=N^T b_S, y_num=N c. The primal and dual certificate conditions are A x_num<=q b and y_num>=0. Tightness and primal-dual equality follow from the inverse identity. On the factor path, precompute x0=N^T b0_S, T=N^T B_S, M=A T-q B and h=q b0-A x0. Then M u<=h is exactly equivalent to the direct primal check. Its translation column vanishes because N^T A_S v=q v. The implementation omits that column after verifying the identity. It still reconstructs x_num for the exact objective value. These identities are independent of any upstream claimed LP complexity result.

The proof requires the same A, b0, B and the same issued factor vector that constructed b. Accepting an unrelated supplied u on the compiled path would be unsound. The API constructs the RHS itself, returns a snapshot backed by immutable bytes and checks current object identity, generation and revision before using the factor path. The solver extracts the factor vector from that snapshot. Raw RHS input has no factor authority, even if its contents happen to equal an affine update. It receives the direct exact feasibility scan. Each inverse entry is owned by one API instance and revision; replacing normals, base RHS or factor matrix invalidates the entry. Input arrays are copied into read-only bytes-backed storage; new views cannot mutate the underlying contents. A shape change to a returned snapshot view cannot alter the stored snapshot. Revision digest covers canonical shapes and little-endian int64 contents of A, b0, B, v. SHA-256 is a revision identifier, not a signature or remote authentication protocol.

The trust boundary is cooperative, serial, in-process Python: trusted implementation and callers using public APIs. Arbitrary Python execution can mutate private state; this is not a hostile-process sandbox, concurrent transaction protocol, signed ledger, durable journal, or Byzantine security scheme. The constructor and engine are trusted; callers must not invoke internal Entry.check directly on untrusted data. Model replacement means a fresh API, fresh solver and fresh cache. This prototype rejects stale/foreign/fabricated snapshot objects rather than silently reusing them. Inputs must be integer, shape-correct and within the conservative exact binary64 input envelope |z|<=2^53-1; integer arithmetic falls back to arbitrary precision when a conservative bound does not certify a safe int64 product. Out-of-envelope results are rejected before entering the numerical LP solver. Exact certificate checks remain mandatory, including after fallback. General infeasible, unbounded, degenerate or ill-conditioned cases requiring alternative basis recovery are outside the tested solver scope; exact rejection raises an error rather than returning an unverified optimum.

## Development workload and comparison

24 sequences, 64 steps each (1,536 LPs), dimensions 8/16/32, dense/sparse/correlated/near-active normals, recurring and mixed RHS changes. One independently seeded root per dimension/family/mode cell. The recurring schedule has structured factors; the mixed schedule supplies raw capacity shocks in half its updates. 1,152 factor updates and 384 raw updates. CTS-10's synthetic generator defines the input source branch; it is not actual order-book or collateral data. All data exposed development; no statistical or causal claim. Cache capacity 8, LRU, two candidate attempts, identical approximate dual ranking and exact acceptance. Lazy compile on eligible scan k=ceil(3d/(d-2)) as in CTS-10.

All four arms share factor construction, snapshot creation, current-authority validation and exact inverse verification. Full reuse always runs warm-started HiGHS (with inverse reuse for its exact certification); direct cache tests directly; lazy_checked additionally recomputes b0+B u and compares with b at every update; lazy_bound trusts only the currently issued factor snapshot and otherwise tests directly. The checked arm also rechecks raw updates, matching CTS-10's behavior. The bound arm uses snapshot.u rather than the separately supplied factor argument. All arms pay update construction; generation of synthetic fixtures and the independent fixture agreement assertion are outside timing. The private SciPy HiGHS interface is inherited from CTS-10. These timings are descriptive CPU timings, not hardware-independent complexity claims.

## Results

All 6,144 policy outcomes agree on exact optimal objective. The three cache policies have identical chosen supports, hits, solver calls and simplex iterations. 809 cache hits / 1,536 updates (52.67%); 727 LP solves and 35,873 simplex iterations versus 1,536 and 69,757 with full reuse (48.57% fewer iterations). 549 hits on 768 recurring updates; 260 on 768 mixed updates. Both lazy policies compile 78 maps and execute 608 compressed scans.

| Policy | Primary seconds | Reordered replay seconds | LP calls | Iterations |
|---|---:|---:|---:|---:|
| Full reuse | 10.042 | 10.062 | 1536 | 69757 |
| Direct | 8.326 | 8.610 | 727 | 35873 |
| Lazy checked | 8.404 | 8.600 | 727 | 35873 |
| Lazy bound | 8.490 | 8.455 | 727 | 35873 |

Bound is 15.45% and 15.97% faster than full reuse, 33.11% and 32.80% faster on recurring sequences. Relative to lazy_checked it is 1.03% slower and 1.68% faster; relative to direct it is 1.97% slower and 1.79% faster. No consistent additional runtime gain from replacing the provenance scan. Keep direct as a strong simple reference. The benefit of bound updates is an explicit API invariant and reduced exact matrix work.

| Policy | RHS construction terms | Primal scan terms | Compilation terms | Redundant provenance terms | Sum |
|---|---:|---:|---:|---:|---:|
| Full reuse | 1032192 | 11010048 | 0 | 0 | 12042240 |
| Direct | 1032192 | 18265088 | 0 | 0 | 19297280 |
| Lazy checked | 1032192 | 14486528 | 1677312 | 1376256 | 18572288 |
| Lazy bound | 1032192 | 14486528 | 1677312 | 0 | 17196032 |

Bound removes 1,376,256 redundant scalar-product terms: 7.41% of the checked partial ledger, 10.89% lower than direct with common construction charged. Counts exclude dual tests, inverse-side products, inverse construction, common setup, hashes, copies, bit complexity and the solver itself. Full reuse has lower ledger but greater simplex work. No claim of total FLOP reduction follows from this ledger.

## Audit and reproduction

Independent exact integer linear solves reconstruct all 1,536 distinct (step,support) pairs, including feasibility, dual sign, exact primal and dual equalities and objective agreement. Verify 1,152 factor constructions and 384 raw fallback branches. In every one of 24 roots: stale, foreign and fabricated snapshots rejected; same-content foreign cache rejected; changed A, b0 and B each reject stale inverse entries; raw cutting constraint rejected; input aliases cannot mutate stored model/snapshot; matching raw updates remain untrusted; returned view metadata isolated; wrong shape, noninteger and corrupted translation identity rejected. 144 attempts to re-enable array writeability rejected. 25 out-of-envelope cases rejected, plus exact large-factor cancellation produces the correct small RHS. These controls test specified failure cases, not a general security proof. The independent reconstruction uses the same SymPy backend as the inverse builder but bypasses the compiled transport. Reordered replay reproduces all 6,144 non-timing records exactly.

Python dependencies: numpy==2.3.5 scipy==1.17.0 sympy==1.14.0. Source includes prior CTS-09 and CTS-10 helpers. To reproduce bounded chunks, run `python cts11.py --start 0 --end 4 --out run0_0.json`, then ranges 4..8 and 8..12. Repeat with `--repeat 1` and run1 filenames. Concatenate in cell order, compare `stable(primary)==stable(replay)`, generate aggregates via `summarize`, and run `python cts11.py --audit-input results.json --out audit.json`. See `reproduce.py` for a single entrypoint. `results.json` contains raw primary records; `summary.json`, `replay.json`, `audit.json` contain aggregate and audit receipts; source digests in SHA256SUMS.json. No neural preflight inference; no confirmation split. No repository commit was made.

## CTS-12 proposal

Make factor snapshots symbolic until a full RHS is necessary. For compiled hits, test M u<=h, then obtain exact objective from x_num=x0+T u, using q v for the translation column; no full b vector required. Materialize b exactly for direct checks, raw updates or fallback solves. Define a proof-carrying output (revision, generation, factor vector, support, exact primal/dual numerators and denominator), with independently verifiable provenance and explicit serialized transaction semantics for deployment. Measure against direct caching, including any materialization deferred to certificate verification and receipts; no benefit is earned by hiding the full RHS work in another layer. Test parameter envelope checks, stale revisions, changed matrices, concurrency and restart/recovery before production use. Real clearing constraints and transaction workloads still need separate specification.
