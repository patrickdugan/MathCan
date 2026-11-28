# CTS-12: symbolic factor snapshots

**Status:** exact algebraic identities and synthetic development benchmark. No training, no independent confirmation claim, no production deployment.

## Mathematical contract

For a revision with fixed integer A, b0, B, let A_S be invertible and choose N,q with A_S^T N=q I, q>0. The numerator of the transported primal vertex is

    x_num = x0_num + T_num u_nontranslation + q v u_translation
    x0_num=N^T b0_S, T_num=N^T B_S[:,1:]

where B[:,0]=A v. The compiled primal condition is R u_nontranslation <= s0, with R=A T_num-q B[:,1:] and s0=q b0-A x0_num. Dual feasibility is N c>=0. Tightness at S and exact dual equality follow from the inverse identity. Weak duality then certifies optimality. The scalar objective is c^T x_num/q. This calculation does not require the full b=b0+Bu.

The symbolic API issues immutable factor snapshots bound to its current owner, revision and generation. If maxabs(b0)+r maxabs(B) maxabs(u)<=2^53-1, the RHS is within the exact solver-input envelope and may remain symbolic. Otherwise it is constructed with arbitrary-precision arithmetic and validated before issuance (including exact cancellation). Raw RHS snapshots always use direct checks. Materialization is memoized per current snapshot; it is required for direct feasibility checks and fallback HiGHS. This is a trusted serial in-process interface, not cryptographic authorization. No assertion is made about hostile Python callers or concurrent transactions.

## Protocol

Fresh synthetic development seeds 38012+100000*family+1000*d+100*mode. 24 LP roots, 64 updates per root, d in {8,16,32}; dense, sparse, correlated and near-active families; recurring structured and mixed raw-factor regimes. Cache capacity 8; at most two candidate bases ranked by floating-point cone score; exact arithmetic accepts certificates. Full warm HiGHS with inverse reuse, direct cache, lazy compiled cache with eagerly materialized RHS, and symbolic lazy compiled cache. The latter two share compilation, routing and fallback policy. Per-root arm order shuffled and changed for replay. Count principal products separately from CPU timings. Timings are sums of per-update measured policy paths including setup; generator and independent fixture checks are outside that ledger. In particular, every symbolic result is materialized after timing for independent fixture agreement, so these are production-path timings, not whole benchmark wall clock. The full solver baseline includes exact verification with inverse reuse.

| Arm | LP calls | Iterations | First run s | Replay s |
|---|---:|---:|---:|---:|
| Full warm HiGHS + inverse reuse | 1536 | 70385 | 9.678 | 10.480 |
| Direct cache | 725 | 35619 | 8.004 | 8.805 |
| Compiled cache with eager RHS | 725 | 35619 | 7.961 | 8.622 |
| Symbolic | 725 | 35619 | 7.861 | 8.422 |

All 6144 policy outcomes agreed exactly on objective values. Cache arms agreed on basis, hits, calls and iterations. Of 1152 factor updates, 442 avoided timed-path full RHS construction (422 recurring, 20 mixed). Construction product terms decrease from 1032192 to 665856; vertex reconstruction terms decrease from 1062720 to 898040. Both compiled arms use the same 14303232 online primal scan terms, 1677312 map compilation terms and 139776 vertex-map compilation terms. Product counts are a partial work ledger, not bit complexity or machine instructions. Exact certificate reconstruction includes big integer work. No neural claim or statistical performance guarantee.

## Audit and replay

All 6144 non-timing records matched. Independent numerator/denominator solves checked all 1536 distinct objective-support pairs; 1152 factor vertex reconstructions agreed exactly with independent solves. 384 raw updates independently checked. 24 each stale/foreign/fabricated snapshot, invalid raw cut and changed-revision controls rejected; 48 immutable-view checks; one overflowing update rejected; a large cancelling update reconstructed exactly. This is finite evidence. Current workloads are synthetic and use a private SciPy HiGHS interface. Initial long process timed out; completed in three chunks per run. No new Lean check. See audit.json and SHA256SUMS.json for provenance.

## Reproduce

Python 3, numpy 2.3.5, scipy 1.17.0, sympy 1.14.0. Run `python reproduce.py` from this directory. It regenerates raw results, summary, replay and audit. Timing fields are not expected to be identical. Original code dependencies are copied from CTS-11. For MathCan, link to the parent certificate-trajectory note and keep dependencies in CTS-11 (copy them to the same directory or add it to PYTHONPATH).

## CTS-13 proposal

Contract only the scalar objective using a precompiled map or dual certificate, skipping even vertex reconstruction for value-only callers. Distinguish value-only receipts from full allocations, charge all materialization at the settlement boundary, and audit stale objectives and exact reconstructability. Real exchange/clearing data and concurrency remain separate gates.
