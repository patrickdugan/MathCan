# CRD-14 | Static resource allocation, receding control and deep likelihood intervals
2026-11-27. Protocol b07e0413e7c7f3109bc2acfa10c3f0cdf98092f6 committed before generation. Finite implementation 239f27d000788c62327d638c4622fe939a42e591, receipt a73f65180c0e7e2dcfaefb92b47cd27414825fec. Deep implementation b4eb20bed824ab97caea39a9136966e881fd44da, receipt fb4cde30fd20a911fd89814cae13580fc6cd13a0, compact deterministic replay summary af9a074797b41e4a5799b8b18f9db3d7cc6ff750. Extension of draft PR #291. Independent synthetic branches with mandatory sensors and mutually exclusive successful terminal states. No new fitted parameters, real proof-search verifier, or integer-factorization result.

## 1. Static allocation theorem
Let V_i(t) be branch i's optimal local success with at most t remaining actions. Given the observed local histories, independent hidden states and sensor noises imply that a fixed sequential allocation t_i, sum_i t_i<=b, has success
    F_t=1-product_i(1-V_i(t_i)).
Stop on success, discard unused actions in a completed allocation, and do not transfer them. With alive branch states and active-capacity>=1, first serve the already-active assigned branches, then the unopened assigned branches; when opening at full capacity, an already-served or unassigned active branch is available for eviction. Thus there exists a legal execution of this plan under the CRD-11 abandonment semantics. Allocations to dead branches have zero local utility. The minimum-failure DP
    D_i(r)=min_{0<=t<=r} [(1-V_i(t)) D_{i+1}(r-t)],
    D_n(r)=1
returns F(s,b)=1-D_0(b) and a witness, in O(n b^2) candidate combinations plus local value computation. For the fixed static plan, independence is required, not just marginal posterior calibration. F is an achievable lower bound on the full adaptive optimum, not its upper bound. The floating-point finite implementation uses tolerance 1e-15 for allocation ties.

One-step receding action score H(s,a,b)=p_hit+sum_{nonterminal o} p_o F(s_o,b-1). A first action of an optimal legal static witness can be followed by a feasible residual allocation on every nonterminal outcome. Any saved actions are allowed to remain unused. Consequently max_a H>=F(s,b). If no actions are feasible F=0. Induction in remaining budget gives V_receding1>=F. The same lower-bound Bellman backups can be repeated: L_0=F and L_{h+1}=T L_h. Since T is monotone and T F>=F, L_h is nondecreasing in h and <=V*. A receding policy selecting an action greedy for L_{h-1} has value >=L_h, by backward induction and L_h>=L_{h-1}. This does not imply closed-loop policy dominance between consecutive h. Action ties quantized at 1e-12 in the implementation; comparisons audited at 1e-10. Two-step policy maximizes the expected one-step backup, then replans at subsequent observations. Local values use CRD-12's direct likelihood formula, no recursive local DP. This theorem pertains to the specific independent-branch legal model.

## 2. Frozen finite benchmark
192 roots, seeds 2040001..2040192, 3 branches with 1..3 sensors, capacity 1/2 and budgets 4/6. No training; original frozen CRD-11 recurrent head uses its original local-DP inputs, all other policies as registered. Same roots used for each cap/budget, not independent replicates. Expected success and calls calculated by finite model recursion, not sampled physical trials.

| Policy | cap1 b4 | cap1 b6 | cap2 b4 | cap2 b6 |
|---|---:|---:|---:|---:|
| Optimal | .582423 | .751870 | .583417 | .755678 |
| Static | .550989 | .661485 | .550989 | .661485 |
| Receding1 | .577606 | .723654 | .578643 | .735665 |
| Receding2 | .582423 | .750997 | .583417 | .755149 |
| Depth | .403842 | .596361 | .403842 | .596361 |
| Marginal | .525547 | .667701 | .525760 | .671370 |
| Sensor-aware | .530016 | .655931 | .533062 | .670513 |
| Local | .568292 | .703463 | .569862 | .719561 |
| Rollout | .569377 | .723501 | .570400 | .735172 |
| Frozen recurrent | .555635 | .696845 | .559641 | .718249 |

Primary cap2 b6: receding2 regret .00052919 (0.05292 percentage points), 175/192 roots tie optimal in value at tolerance 1e-12; 17 below, none above. First action differs from optimal on 56/192 roots; equal utility can have distinct optimal actions. Receding2 gains vs recurrent +.0368998, paired 95% percentile bootstrap [.0309424,.0431964], 150 wins/0 losses/42 ties. Vs rollout +.0199768 [.0141249,.0260597], 88/1/103; vs receding1 +.0194840 [.0152381,.0238992], 101/2/89; vs static +.0936643 [.0845097,.1026787], 181/0/11. Receding1 vs static +.0741804 [.0653060,.0833776], 179/0/13. Receding1 vs rollout +.00049287 [-.00509324,.00633185], no identified superiority. Receding1 vs recurrent +.0174158 [.0112690,.0236539]. Bootstrap 2,000 root resamples, descriptive unadjusted intervals.

Primary expected action costs: static 4.14202, receding1 4.93599, receding2 5.02529, exact optimum 5.00506, recurrent 4.36966, rollout 4.95835. Equal maximum budgets do not imply equal expected actions or inference cost. Receding2 expected evictions .03602, exact .03384, frozen recurrent .00248. At cap1 b6 receding2 .27949 evictions/root vs exact .28398; no isolated eviction-policy causal effect established.

## 3. Work accounting and verification
Totals at cap2, both budgets, 192 roots, memoization shared across budgets:
| Policy | Local DP transitions | Formula pattern leaves | Allocation combinations | Lookahead outcome scores | Policy-evaluation states |
|---|---:|---:|---:|---:|---:|
| Static | 0 | 5,308 | 24,768 | 0 | 5,081 |
| Receding1 | 0 | 11,176 | 556,323 | 44,108 | 7,323 |
| Receding2 | 0 | 12,268 | 1,167,051 | 202,884 | 7,390 |
| Frozen recurrent | 134,423 | 0 | 0 | 0 | 6,360 |
| Rollout | 0 | 0 | 0 | 43,347 | 7,176 |
| Optimal | 0 | 0 | 0 | 0 | 156,082 |

Rollout also computes 41,361 continuation-policy states and 78,972 continuation transitions. Exact oracle 967,031 outcome transitions and 485,354 candidate actions. Receding2's global allocation solves 70,088 distinct state/budget DP instances and 59,562 cache hits. It can nearly match optimal utility while visiting fewer policy-evaluation states, but the per-state allocation work is substantial. Different counters are not identical operations. No runtime advantage established. All caches currently unbounded. The reported JS isolate 21.932s includes generation, policy evaluation and audits, not a controlled inference-time measurement.

7,680 policy/root/cap/budget expected-value evaluations; 768 executable static witness equality checks including legal capacity, budget and action accounting; 64 brute-force static allocation comparisons over 3,808 feasible allocations; 2,688 static budget monotonicity checks; 48,315 one-step Bellman lower-bound inequalities across policy and lookahead states (minimum slack -2.22e-16); 768 realized receding1>=static policy checks; 16 independent forward world replays over 3,456 worlds, max discrepancy 9.99e-16. No failures. Independent forward replay evaluates chosen actions under latent-world/sensor outcome enumeration, not an independent proof of the optimal DP. Exact finite model means exact expectation up to floating arithmetic. No actual proof-verifier calls.

## 4. Deep local intervals imply exact allocation certificates
For V_i(t) in [L_i(t),U_i(t)], monotonicity of 1-product(1-V_i) implies
    max_t [1-product(1-L_i(t_i))] <= F* <= max_t [1-product(1-U_i(t_i))].
Both maxima computed using failure-product DP. If lower-selected plan t has lower value exceeding every distinct plan's optimistic upper value, it is the unique static optimizer even when its actual value is uncertain. Weak inequality certifies optimality (ties possible). A tighter selected-plan regret upper bound is max(0, max_{other plans} U_plan-L_selected), rather than the full optimum interval width. Merely attaining both the lower and upper relaxed optima is insufficient by itself. These are exact rational statements for the static policy class, not upper bounds for adaptive optimum.

36 disjoint roots (12 each weak/moderate/high), 108 branch fixtures, depths 12/32/64 in rotated order; 46- and 78-action budgets. Each branch either skipped or given m+k actions for k=1,2,3. k3 exact feasible mass; k1/2 from CRD-13 original and combined TV/overlap solver. Branch i has one denominator D_i for all four options. Multiplying failure numerators and comparing with common denominator product_i D_i gives exact BigInt allocation bounds without rational rounding. Depth12 raw enumeration checked both k1/2 on all 36 roots; no exhaustive truth for depths32/64. 64-depth branch inaccessible at B46. At B78 it is accessible, but cannot be jointly funded with 32-depth. Feasible allocation counts 8/20 at B46/78. DP comparisons to exhaustive enumeration for every cap/engine/expansion combination; all 576 comparisons and interval nestedness checks pass, 72 exact depth12 local references contained. Total 108 branch fixtures; no new latent model fitting. All output decimal probabilities are displays of exact integer ratios.

| Signal | B | Original width (pp), 512 expansions | Combined width (pp) | Combined optimal plans certified /12 | Unique /12 |
|---|---:|---:|---:|---:|---:|
| Weak | 46 | 9.22369 | 0 | 12 | 12 |
| Weak | 78 | 0 | 0 | 12 | 12 |
| Moderate | 46 | 12.69448 | 9.21783 | 12 | 12 |
| Moderate | 78 | 1.86793 | .82788 | 8 | 1 |
| High | 46 | .05970 | .04872 | 12 | 12 |
| High | 78 | .02954 | .02526 | 12 | 7 |

At B46, combined weak and high certify all 12 unique static plans at zero internal expansions; combined moderate does so by 128. For weak at B46 exact objective 0.68415665 averaged over roots, because all selected plans can probe all feasible states of one branch, and competing optimistic intervals are dominated. At moderate B46 mean combined optimum interval [.67631007,.76848840] at 512; all selected plans nevertheless proven optimal, because their lower bound dominates every distinct plan's upper bound. This is the key distinction between value accuracy and decision accuracy. At B78 moderate only 8/12 certified optimal; average alternative-regret bound .0047832 (0.47832 pp), not a claim each root is within that mean. High-signal narrow bounds depend on engineered separation. No uniform efficiency claim across regimes. At 512 expansions max local heap 513. The current batch computes all local k1/2 bounds even on branches inaccessible at B46 and even when a global certificate could have stopped earlier. Work counters are not measured bytes. Original/combined may follow different expansion orders; no universal fixed-budget dominance theorem.

## 5. Reproduction and limitations
    node research/certified_recursive_descent/global_allocation.mjs
    node research/certified_recursive_descent/global_allocation_intervals.mjs
Executed concatenated source bodies in JS isolate with frozen dependency blob checks. Full deep receipt creation succeeded and GitHub returned blob fbea8e3e41600123810fe5e56b6cca044bb463bf; connector readback returned empty body. Reexecuted the deterministic deep sweep (all checks passed) and published compact summary, successfully read back at blob 79742571957ea4232c9255cf161571f57ab32792. No full-receipt byte-level readback comparison claimed. Added import guard/export to frozen CRD-13C module for reuse, no algorithm changes. Standalone Node CLI verification, hosted checks on new PR head, actual physical RSS and latency profiling, Lean compilation and Cogentic original proof audit not established.

## 6. CRD-15 proposal (unregistered)
Use the proven achievable static F as a Bellman lower envelope. An admissible optimistic upper envelope U can relax information acquisition by revealing hidden feasibility for free: at a given state any successful branch must have at least m_i+1 remaining calls to finish mandatory sensors and one probe. Under independent branch posteriors, the probability that any individually affordable branch is feasible is a valid upper bound on full adaptive success. This prophet bound ignores competition for shared resources and abandonment, and can be loose. Repeated monotone Bellman backups can tighten lower/upper envelopes, using terminal boundary conditions. For a fixed information state, an action with lower continuation score greater than every competitor's upper can be chosen without resolving all values. Implement budgeted proof-guided Bellman refinement, with interval overlap deciding where to spend more local likelihood or global outcome expansion work. Compare full exhaustive DP, fixed one/two-step allocation, selective refinement, local/formula head, and learned proposal with exact fallback on fresh roots, including tight-cap and deeper sensor settings. Charge node/edge work, cache occupancy, and actual CPU/RSS if available. Evaluate correlated branches separately with CRD-09 posterior messages, not independent products. No proof-search or number-theory transfer established yet.
