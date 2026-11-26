# CRD-09 | Dependency-aware memory and failure evidence
2026-11-27. Protocol commit 32a3be284d4a3649f02cfafc31aab9993c092eba, registered dense source commit 6d749f2a7c1b7258b3a015ccbafb242ca12bd4f3, dense receipt eb1a23bcd70c2cc1bef042e9764dcc7d3ccec9ae. Post-hoc factorized backend dc3f0538623d661c46237b2327a0737e3b8d7c17, equivalence receipt 318ec7cfc9b739a7e433c5b727dd8b252760ebce. Positive primary conditional expected-utility result on engineered correlated trees; independent control null as predicted. No new training; reuse CRD-08 frozen learned operators. No full BPD/TRM or factoring result.

## Exact evidence inference
For a reached tree with finite hidden state space, let l_v be the local evidence likelihood, T_vw a row-stochastic edge transition, and pi the root prior. Conditional independence of child subtrees gives

    m_v(x) = l_v(x) product_w (T_vw m_w)(x),
    Z(E) = pi m_root.

The posterior of a queried node v is obtained by propagating the root prior down its path, multiplying by the parent evidence factor and sibling upward contributions before each transition. Multiply the resulting cavity row by m_v and divide by Z(E). All factors for failed terminal probes are l_v(x)=1{x != target}. The posterior updates include evidence from failed branches even if those branches have left the candidate bank. Exact inference uses only reached edges in the adaptive task. Future edges are integrated under the public token/noise law. Observing a new edge and a child with no outcome evidence contributes the unit vector to its parent, so no ancestor update is needed. A failure changes only the ancestor path. For binary trees, dense edge matvecs take O(d^2) time per edge for d states, and each cache update or individual posterior query uses O(H d^2) operations for path height H. Computing all posterior marginals by a full upward/downward pass uses O(|E|d^2); the implementation here uses individual path queries. The upward and child-contribution vectors occupy O(|V|d) numeric state; count additional shared operator tables and forecasts separately. No division by individual child messages is required, avoiding problems when they contain zeros. Learned evidence normalizers <=1e-14 have a defined prior fallback; receipt counts it.

Four depth-2 fixtures were enumerated independently in hidden group coordinates, with rational transition denominator 600. All 186,624 latent assignments, 64 evidence masks and 128 remaining-candidate posterior checks passed. Maximum absolute discrepancy 4.45e-16. A separate cached-vs-full recomputation comparison checks 1,312 queried probabilities per regime (2,624 total), max discrepancy 6.11e-16. Independent terminal replay reconstructs the ordered hidden path via permutations on three points. Arithmetic edge checks use the CRD-01 verifier and independent BigInt inequalities. These are bounded checks supplemented by the derivation, not a formal Lean theorem.

## Primary probe-only result
192 fresh roots per regime, depth three, eight terminal candidates. First-level transitions have reset rate .60/.80; later edges 0/.05/.15. The independent control replaces final transitions by uniform resets. Every prefix edge checked before scheduling; 14 prefix calls common. Every policy can choose at most k terminal probes, stops at the first success. The full all-failure action order is deterministic given observations, so a policy's conditional success is exactly 1-Z(E_all_fail), even with adaptive feedback before stopping. Exhaustive oracle enumerates all size-k subsets and orders the chosen subset by marginal score (not necessarily minimum expected probes); ties between quantized subset objectives follow lexicographic enumeration, within-subset ties descending node ID. Exact scores rounded to 1e-12 for ranking only. Expected utility and regret averaged across the frozen observed trees are the primary endpoints, not observed binary significance.

| Correlated | k=2 expected % | k=4 expected % | k=2 actual /192 | k=4 actual /192 |
|---|---:|---:|---:|---:|
| Depth/node-ID | 27.3978 | 41.9365 | 54 | 73 |
| Random | 29.9984 | 47.9541 | 46 | 80 |
| Known marginal | 37.6286 | 51.2050 | 71 | 86 |
| Learned marginal | 37.1726 | 50.6063 | 67 | 83 |
| Ancestry diversity | 38.5296 | 52.3579 | 73 | 94 |
| Known feedback | 42.7662 | 58.6340 | 74 | 105 |
| Learned feedback | 42.7188 | 58.6225 | 75 | 102 |
| Exhaustive optimum | 42.8088 | 58.8121 | 76 | 99 |

Known feedback expected gain vs known marginal: +.0513763 and +.0742897; versus diversity +.0423656 and +.0627610. Mean regret against optimum .000425872 and .001780652. Learned feedback regret .000899809 and .001895636. In k=2 known feedback vs marginal, observed 8 wins/5 losses, paired p=.581; vs diversity 10/9, p=1. Binary observed scores do not establish significance for these comparisons. The oracle optimizes conditional expected success, so lower realized solve count than greedy at k=4 is sampling variation. Known feedback changes the all-failure order on 129/192 roots vs known marginal at k=2. Exact oracle enumerates 18,816 subsets per regime, 263,424 edge matvecs each, excluding ordinary policy evaluation diagnostics.

Independent terminal resets make all eight terminal states iid uniform conditional on observations. Every policy's true expected success equals 1-(5/6)^k, checked on every root for both budgets, 30.5556% / 51.7747%. Known feedback and known marginal have identical probe orders and outcomes. Numerical regret residues around 1e-16 are rounding. Other policies may differ in actual solves because of tie orders; no true utility gain. Learned model is slightly misspecified at reset c=1; its utility is evaluated under the true law. 116/192 correlated trees and 147/192 independent trees actually contain a target terminal among all eight; no filtering out infeasible roots.

## General mathematical result: greedy coverage under arbitrary dependence
For success events A_i on a common probability space, define F(S)=P(union_(i in S) A_i). For S subset T, F(S+i)-F(S)=P(A_i intersect all failures in S) >= P(A_i intersect all failures in T)=F(T+i)-F(T). Thus F is normalized, monotone and submodular without any independence assumption.

For a fixed probe budget k and success-only stopping, at an all-failure prefix S with P(all fail)>0, the marginal increase from probing i is

    Delta(i|S) = (1-F(S)) P(A_i | all probes in S fail).

Consequently ranking by exact conditional success after every failure is precisely the usual greedy maximization of F. For an optimal size-k subset O, submodularity gives max_i Delta(i|S) >= (F(O)-F(S))/k whenever F(O)>=F(S). Iterating the residual-gap bound yields

    F(S_k) >= [1-(1-1/k)^k] F(O) >= (1-1/e) F(O).

If failure probability is zero, utility is already one. This bound applies to fixed observable candidates with a single success/failure result and stopping after success. It does not establish a guarantee for adaptive expansions that reveal new candidates or richer observations, variable-cost probes, or an arbitrary learned utility.

For approximate conditional estimates with uniform error epsilon_t at step t, the chosen marginal gain is within 2 epsilon_t (1-F(S_t)) of the best true gain. Therefore, with alpha=1-1/k,

    F(O)-F(S_k) <= alpha^k F(O)
      + 2 sum_(t=0..k-1) alpha^(k-1-t) epsilon_t (1-F(S_t)),

when the optimal comparator has size k. A coarser bound replaces failure probabilities by one. This gives a conditional downstream scheduling guarantee without an independent-product approximation. Error assumptions must be checked on the actual failure histories, not merely averaged unconditionally. This is a derivation, not a Lean-checked theorem.

## Adaptive branching (secondary)
192 fresh trees per regime, depth 4–6, edge symbols only exposed after checked expansion. All edge and terminal checks count against one ceiling; learned and known operators use the same depth-preserving forecast from a node's posterior and the public future mean transitions. Posterior feedback updates the whole reached tree. Node-ID ties explicit. Diversity heuristic uses a fixed ancestry penalty relative to failed terminals.

| Solved /192 | Corr cap4/24 | Corr cap16/48 | Indep cap4/24 | Indep cap16/48 |
|---|---:|---:|---:|---:|
| Depth | 115 | 162 | 140 | 188 |
| Depth/random | 118 | 167 | 142 | 186 |
| Known marginal | 116 | 164 | 140 | 188 |
| Learned marginal | 119 | 166 | 145 | 187 |
| Known feedback | 122 | 166 | 140 | 188 |
| Learned feedback | 124 | 168 | 146 | 187 |
| Diversity | 116 | 164 | 140 | 188 |

At correlated cap4/24, known feedback vs its own marginal baseline 6/0 paired wins/losses, p=.03125; learned feedback vs learned marginal 5/0 p=.0625. Known feedback vs depth/random 41/37 p=.734, learned feedback vs depth/random 43/37 p=.576. No broad adaptive superiority established. All paired tests are descriptive and unadjusted; the predeclared primary endpoint is probe-only expected success. Mean charged calls known feedback 18.229 vs marginal 18.281; learned feedback 17.969 vs learned marginal 17.995. The exact filter is only the correct belief conditioned on observed evidence, not the globally optimal expansion policy; score uses mean future transition, not lookahead maximization. Diversity yields the same aggregate outcomes and work as known marginal in these configurations. The independent control gives exact known feedback no utility advantage. Learned-operator gains over the true model are not established.

## Cost accounting and factorized backend
Probe-only: 6,144 logical policy/root/budget episodes, 5,376 actually executed shared prefix checks (86,016 logical prefix calls), 15,022 terminal probes. Adaptive: 5,376 episodes, 107,615 charged verifier calls. Total 11,520 logical episodes, 128,013 executed prefix/terminal checks across the registered experiment, excluding audit/replay computations. Zero false accepts. Inference-only enumeration, posterior evaluations and independent arithmetic checks are reported separately, not treated as extra verifier calls. Probe-only costs measured up to actual stop in the preplanned all-failure order (planning/diagnostic work beyond stop is not policy runtime). At correlated k=4, known feedback uses 1,059 upward and 11,073 downward edge matvecs vs marginal 0 and 4,608. Cache 174 float64 slots (1,392 bytes) per full depth-3 tree (up + edge vectors). Adaptive maxima 222 / 414 slots (1,776 / 3,312 bytes) for caps4/16, excluding current query scratch, map objects, IDs, forecast matrices, fixture and shared transition data. Operator tables 864 slots (6,912 float64 bytes) across both models and regimes in the execution; optional permutation metadata 168 additional numeric entries (not measured memory). Cache tracks all observed nodes, so its size scales with reached tree, not just bank cap. No physical RAM or CPU throughput benchmark.

For reset-permutation T=(1-c)P+cJ, J all entries 1/d, both matvec directions admit O(d) arithmetic:
    (T m)_i = (1-c)m_perm(i) + c mean(m)
    (p T)_j = (1-c)p_perm^-1(j) + c sum(p)/d.
This avoids dense per-edge O(d^2) work; arbitrary future product matrices still use dense readout. Added optional --factorized backend after the frozen dense result. Replayed the full registered experiment at the same seeds, compared 1,797 receipt fields (excluding elapsed time), max absolute numeric delta 6.218e-15, zero mismatches at tolerance 1e-9, all observed counts unchanged. This is aggregate receipt equivalence, not a claim of bitwise identical individual traces. Optional mode still stores dense matrices, so no operator-storage saving claimed. Source-body execution checked in JS isolate. Standalone Node invocation not performed. Isolate elapsed 16.720s dense and 11.127s optional mode, including generation, audits, oracle and diagnostics; uncontrolled timings not an isolated speed measurement. Reproduce from repository root with node research/certified_recursive_descent/dependency_aware.mjs (append --factorized for optional mode).

## CRD-10 proposal (unregistered, unexecuted)
Separate exact posterior computation from search policy and inference resource allocation. Implement a two-pass cached message scheduler and a persistent branch-moment bank, storing compact reset-permutation operators instead of dense matrices. Compare path queries, batched two-pass queries, selective stale-message updates with certified error envelopes, and a learned low-rank residual where useful. For a cap of B bytes, include both bank and evidence-cache costs; test fixed physical memory and total CPU budget alongside verifier calls. Construct adaptive expansion instances with information gain that changes which branch should be expanded, and exhaustive small-tree decision oracle with branch observation costs. An empirical full-policy gain is required beyond marginal depth, exact feedback, and inexpensive diversity. Also isolate the case where feedback is valuable for eviction (CRD-08/09 do not establish it). Consider dependence-aware group/Fourier blocks as BPD components, with cached evidence factor multiplication separated from operator transport. No factoring or ECDLP result. The original Cogentic PDF and Lean formalization remain unaudited; CRD-01 Lean ledger uncompiled.
