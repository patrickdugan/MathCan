# CRD-02 | Coupled descent and budgeted certificate search
2026-11-26. Synthetic CPU search results, not a trained model or a factoring implementation. Extension of CRD-01.

## Coupled asymptotic closure

Let the finite phase set have costs T_i(n)>0, finite on every integer n>=2. Let Lambda be defined as in CRD-01. Assume for each phase, sufficiently large n, and any epsilon>0,

    T_i(n) <= K [ exp((a_i0+epsilon)Lambda(n))
        + sum_{i->j} exp((a_ij+epsilon)Lambda(n)) *
             (1 + max_{2<=m<=n^beta_ij} T_j(m)) ],

with finite edge set (parallel edges allowed), K>0, nonnegative a_i0 and a_ij, 0<beta_ij<1. Coefficients a_ij must account for the actual expected multiplicity, including retries; they cannot be inferred from the size bound. Define r_ij=beta_ij^(1/3). If all C_i>a_i0 and C_i>a_ij+r_ij*C_j, choose epsilon smaller than the minimum strict slack. For all sufficiently large n, the finite prefactors (including K and the number of edges) fit into the remaining exponential slack. Choose M>=1 dominating all finitely many base values. Induct simultaneously on n (children are strictly smaller); use Lambda(m)<=r_ij Lambda(n) for large n. Each summand is bounded by a fixed multiple of M exp((C_i-delta)Lambda(n)), hence T_i(n)<=M exp(C_i Lambda(n)). This proves limsup log(max(1,T_i(n)))/Lambda(n)<=C_i.

The upper-envelope map F_i(C)=max(a_i0,max_{i->j}(a_ij+r_ij C_j)) is monotone and a contraction in sup norm with rate max r_ij<1. Its unique nonnegative fixed point is the least nonnegative supersolution: iterate F from zero or use monotonicity on any supersolution. Adding a positive constant to every coordinate of the fixed point creates strict slack at least (1-max r)*constant. This establishes the limiting conditional bound. Replacing r with verified rational upper bounds gives an exact finite certificate (cube comparisons and linear inequalities); the upper envelope can be conservative.

Toy system with local exponents below 15: a_01=4,r_01=4/5; a_10=7,r_10=1/2. Child exponents beta_01=1/2,beta_10=1/8 satisfy r^3>=beta. The rational-envelope fixed point is (16,15) and (17,16) is a strict certificate. The executable checks reject the equality case under the strict-certificate protocol. This is a mathematical argument and exact toy arithmetic; no compiled Lean theorem for this extension yet.

## CRD-02 search specification

A root is a directed layered DAG. The initial node is start and a terminal goal is selected during generation. At each visited nonterminal node, the policy receives its outgoing candidates in a shuffled order. Every proposed edge carries the CRD-01 rational certificate; the exact verifier checks the local inequality, then checks whether the target is the goal. Valid paths may terminate at non-goal leaves or reconverge. At least one valid path is planted and independently checked by offline shortest-path DP. The policy may not query that DP, the hidden planted path or unvisited adjacency. This is a synthetic proof-graph search task; graph connectivity is not inferred from integer factoring.

Candidate order is deterministic for each seeded root and shared across retention arms. RNG uses mixed 32-bit seed outputs. Three disjoint splits: development 96 roots, depths 4-5, width 6, outdegree 3, denominators 7/11; validation 48, depths 6-7, width 6, outdegree 3, denominators 13/17; held-out 96, depths 8-10, width 9, outdegree 4, denominators 19/23. All graph experiments are exploratory classical baselines. For future neural benchmarking freeze a new unseen test seed range before training or inspecting model results.

Every attempted edge, invalid or reconvergent, consumes one verifier call. One active candidate list is available to all arms. A depth-first bank holds deferred candidates from previous nodes; on overflow evict the oldest candidates. Capacity is a count of deferred edges, not total memory or bytes. All arms keep reached nodes and parents within an episode; these shared data structures and the fixture are outside the bank capacity. Cap zero follows a single path, trying locally invalid edges until the first new valid child and discarding alternatives at the parent. Random restarts reset the episode cache and shuffle adjacency order after the first attempt, charging all calls across attempts; no bank. Report both total calls and success under a common ceiling. Retention can stop early after exhausting its retained frontier; the experiment matches ceilings, not realized calls. Independent replay checks certificates, reached-frontier membership, no repeated edges within an episode, counts and final paths; the cap check relies on instrumented peak deferred count.

Run from repository root: node research/certified_recursive_descent/search.mjs
The checked-in receipt contains all budgets 8/16/32/64/128 and caps 0/4/16/64/unbounded plus restart. Final sweep: 240 roots, 9,916 episode replays, 127,991 charged calls. Held-out depths: 24 at 8, 29 at 9, 43 at 10. The initial exploratory run was superseded after seed mixing, addition of a restart control, and correction of an equality-case test. All reported results use the final sweep. The repository code was executed in a JS isolate using the source bodies; Node module invocation and Lean compilation remain separate checks.

| Held-out solved / 96 | 32 calls | 64 calls | 128 calls |
|---|---:|---:|---:|
| Single path | 10 | 10 | 10 |
| Random restart | 16 | 37 | 55 |
| Deferred cap 4 | 31 | 37 | 37 |
| Deferred cap 16 | 47 | 86 | 95 |
| Cap 64 or unbounded | 47 | 86 | 96 |

At ceiling 64, cap 16 and full retention tie at 86/96; cap 16 beats random restart on 49 paired roots with zero losses and averages 35.5 calls versus 53.15625. Cap 4 at 128 is worse than restarts (37 versus 55); a small bank can discard crucial alternatives. Cap 16 loses one root versus full retention at 128. Maximum observed deferred count under full retention was 27 for held-out. This establishes baseline behavior on generated DAGs, not a learning gain or actual RAM speedup.

## Next model experiment: CRD-03

Compare FIFO/DFS, cap-matched random eviction, random restart, and a learned cap-matched priority/eviction policy. A verifier-first arithmetic heuristic is mandatory: certificate inequalities are public and cheap to compute, and any attempt to evaluate them counts toward the budget. Include an exact full-information shortest-path reference separately as an oracle, not as a budget-matched search policy. Input is only the reached frontier, certificate features, depth, and budget. No target leakage from labels, hidden paths, future nodes, episode seeds, or output ordering. Charge policy wall time, CPU time, actual peak RSS, and verifier calls; use equal training data and update ceilings. Candidate retention gains must be measured against cap-16 DFS and cap-64 DFS, not only single-path. Use fresh seeds and freeze training/validation/test protocol first. Candidate retention is a search mechanism, not yet a BPD factorization or learned steering intervention.

## Source audit status

The pinned Cogentic PDF still failed through GitHub binary fetch and raw web retrieval (unsupported binary content-type); the formalization is still absent from the inspected directory. Secondary accounts describe polynomial generation, prime descent, local square certification and recursive factoring, but those reports are not substitutes for the precise premises. All mathematical conclusions in this note are conditional on the stated recurrence. No cryptographic security or factorization-complexity result is inferred from this synthetic gym.
