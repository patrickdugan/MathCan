# Certificate–trajectory separation and parametric LP certificate transport

**Status:** written elementary algebraic proofs and finite synthetic development evidence. Imported from CTS-01–11 (EvalMath). Full upstream theorem verification and production clearing validation remain open.

## Motivation and source provenance

[OpenAI math, family 380, pinned at 3344da5](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/380.md) reports strongly polynomial rational LP and superpolynomial diameter for simple rational polytopes even under limited face moves. These claims motivate separating computational cost from representation-restricted path length. They are cited claims, not proved here. The independent polygon example and earlier learned-policy investigations are in [EvalMath PR #80](https://github.com/MoralityLabAI/EvalMath/pull/80), including [CTS-01](https://github.com/MoralityLabAI/EvalMath/blob/5351c66ff97a17bc6dcebb80d10b6ba3bfc9a4ce/paper/certificate_trajectory_separation.md) and [CTS-03](https://github.com/MoralityLabAI/EvalMath/tree/578e40648b92bde80191c31a7cb50d02f63f0ba1/research/cts03). CTS-04–08 trained compact recurrent selectors and explored certificate memory; those checkpoints remain separate sandbox artifacts. This MathCan note owns the algebra and source-backed classical experiments from CTS-09–11.

## Theorem 1: exact parametric certificate region

Fix rational A (m by d), b0 (m), B (m by r), an ordered set S of d row indices with A_S invertible, and P=A_S^{-1}. Consider max c^T x subject to Ax <= b0+Bu. Define

    x0=P b0_S, T=P B_S, M=A T-B, h=b0-A x0.
    x(u)=x0+Tu, y_S(c)=P^T c.

Extend y by zeros outside S. The pair (x(u),y(c)) is a primal-dual optimal certificate exactly when M u <= h and P^T c >= 0. Proof: substitution gives primal feasibility iff M u<=h; A_S x=b_S and A^T y=c hold identically. Dual feasibility is precisely y_S>=0. Then c^T x=y_S^T A_S x=y^T b, and weak duality proves optimality. This is an iff for the specified basis certificate; a degenerate optimum may admit a different certifying basis. The product of the primal factor polyhedron and the dual normal cone gives a region on which one basis suffices. For fixed c, the value is affine in u; for variable c, the value c^T(x0+Tu) is bilinear plus linear terms.

The implementation uses integer numerators: A_S^T N=q I for positive q. Then x_num=N^T b_S, y_num=Nc, primal feasibility A x_num<=q b, dual feasibility y_num>=0. The compiled map uses x0_num=N^T b0_S, T_num=N^T B_S, M_num=A T_num-qB, h_num=q b0-A x0_num. These tests are exact over arbitrary-precision integers with guarded fixed-width fast paths.

## Theorem 2: translation cancellation

If B_j=A v for a rational vector v, then T_j=P A_S v=v, hence M_j=A v-B_j=0. Thus factors translating the entire feasible region have no effect on primal feasibility of the transported basis. They still change the vertex and objective value. More generally, every direction z with Bz in im(A) belongs to ker(M); the induced primal check factors through the quotient by those directions. Proof follows by linearity and the same substitution. The experiments explicitly check a translation column; general quotient-basis compression remains proposed.

## Theorem 3: online compilation under a fixed work model

Suppose one active basis receives h eligible tests, each direct check costing D, compiled check R<D, and one-time compile cost C>0. Offline cost is min(hD,C+hR). Let delta=D-R and k=ceil(C/delta). Rent for at most k-1 tests, and compile before performing the kth eligible test. If h<k, the direct cost equals offline; if h>=k, excess above hR is (k-1)delta+C < 2C, while offline excess is C. The total cost is therefore at most twice offline in this model, including the common hR. At r<d, a dense principal-matrix work estimate for affine compilation has break-even h>d(r+1)/(d-r). The theorem does not cover changing per-test costs, eviction policy, time overhead or bit complexity. Apply the bound separately to each cache-residency episode.

## Revision invariant and symbolic extension

The compiled predicate is sound for a factor snapshot issued against the same immutable (A,b0,B) revision. An arbitrary supplied u is not a witness for unrelated b. CTS-11 binds cache and snapshot ownership to an in-process object/revision/generation, constructs b itself, and rejects stale, foreign or fabricated snapshots. A raw RHS uses direct exact checks. This is a cooperative serial API invariant, not cryptographic authentication, concurrent transaction safety or a general proof against hostile callers.

CTS-12 proposal: delay full RHS materialization; reconstruct x_num=x0_num+T_num u only when a compiled certificate is accepted, materialize b on direct verification or numerical fallback, and charge independent verification to the ledger. Revision-bound receipts and an authenticated transaction protocol are separate obligations before production.

## Evidence and reproducibility

- [CTS-09 report](cts09/README.md): 768 synthetic LP updates, 3,840 policy outcomes, 175 LP solves avoided. Exact transport and affine-compression agreement; preprocessing overhead.
- [CTS-10 report](cts10/README.md): 1,536 LP updates, 6,144 policy outcomes, 784 LP solves avoided; 80 lazy compilations versus 605 eager.
- [CTS-11 report](cts11/README.md), [summary](cts11/summary.json), [independent audit](cts11/audit.json): 1,536 updates; 6,144 exact objective agreements and deterministic non-timing replay; 809 LP solves avoided, 35,873 versus 69,757 simplex iterations. Revision binding removes 1,376,256 redundant scalar-product terms. Two timing runs show 15.45–15.97% lower runtime than full warm HiGHS with inverse reuse; the simpler direct cache remains competitive. These are synthetic, exposed development results.

The CTS-11 directory contains the original report, source modules, reproduction entry point, summary and audit. The original archive manifest lists additional locally archived files (raw results and replay aggregates) omitted from Git; the script regenerates these and tests deterministic non-timing agreement. Recorded timings are historical and will vary. The original archive SHA-256 is f8bba00d58f19ac27792f7d9d58afc91dd101ab5b9dfc69d285fb8985e87050c. All imported text sources and available receipts were checked against sandbox Git blob hashes. No new Lean claim or kernel check; no new confirmation or timing run performed for this import.

From the repository root:

    python -m pip install numpy==2.3.5 scipy==1.17.0 sympy==1.14.0
    python research/certificate_trajectory/cts11/reproduce.py

The benchmark uses a private SciPy HiGHS interface and the pinned environment. The raw files produced by reproduction should not be treated as identical in byte-level timing fields. See the original report for the full workload, overflow envelope and solver scope.

## CTS-12 update

[Symbolic factor snapshots](cts12/README.md) implements the proposed lazy materialization with an exact solver-input envelope and cached affine vertex map. The original source and audit are byte-identical to the sandbox files. Across 24 synthetic roots, 442 of 1,152 factor updates skip timed-path RHS materialization; all 6,144 policy records agree on exact objective values and replay identically excluding timing. Run `cd research/certificate_trajectory/cts12 && PYTHONPATH=../cts11 python reproduce.py` to regenerate raw results, summaries, audit and replay. The archive manifest includes dependencies in CTS-11 and larger raw records omitted from Git. The timing evidence is descriptive, with independent fixture reconstruction outside the measured policy path.
