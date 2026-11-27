# CRD-15 | Selective Bellman refinement with action certificates
2026-11-27. Protocol ba4dfeaac659305ceea4e938e4bd59a77d0a8cc9; frozen selective implementation 3134a653365abecc509ce487af836095ffc535dc. Standard receipt 2dee170f40879d0e965a14d42f9491ac7036c2f2, blob 983efa9fa6b85ec83aff3cb31b2ac605cf7fb9b4. Stress receipt c6a0fbccdfb5c76976946fd46fa42454a88e6571, blob a8124ba6a0740fba74f34444c88aec52f4cde7dc. Both receipts read back and parsed successfully. Prior allocation source only received import guard/export dc58582acf23d90cb63903b09ae0f5cf7fa34bd5 for reuse. No policy fitting, test tuning, new theorem-proving or integer-factorization result. Unlimited numerical certification passes; primary 16-node ceiling trades reduced allocation combinations for lower utility than the two-step baseline. No overall compute superiority established.

## Bounds and refinement
The CRD-11/14 task has independent hidden states, branch-local conditionally independent sensors, unit action costs, mandatory sensor sequence, mutually exclusive successful terminal probes, and irreversible abandonment at full active capacity. For state s with remaining b, initialize lower F(s,b) by the best legal static allocation:
    F(s,b)=max_(sum t_i<=b) [1-product_i(1-V_i(t_i))].
Let I(s,b) be alive branches whose remaining sensor count m_i plus one probe fits b; mass_i is their current total probability of feasible hidden states. A success is contained in the union of feasible-state events for these branches. Thus U(s,b)=1-product_(i in I)(1-mass_i) is an upper bound, even after relaxing capacity and revealing the hidden state for free. The independence assumption is needed for the product. Zero affordable branches gives exact zero. If one branch affordable, exact local V_i(b) suffices: spending calls outside it cannot make any other branch affordable. If all affordable branches have completed sensors, all future nonsuccess observations are failures of probes. A deterministic policy's all-failure order defines a fixed probe set with sum of costs <=b, and local optimal probes plus a static allocation attain the best probability. This yields exact F. These shortcuts use the specified task, not arbitrary correlated or adaptive sensing models.

For each expanded state and legal action a,
    L_a = p_hit + sum_o p_o L(s_o,b-1),
    U_a = p_hit + sum_o p_o U(s_o,b-1).
Since true Q is the same expression with V*, its value lies in [L_a,U_a]. Intersect a state's existing interval with [max_a L_a,max_a U_a]. Each observation consumes one action, so the state-budget graph is acyclic. Cache transpositions and reverse parent links; propagate updated child intervals upward by increasing remaining budget. Initialize each child from F/U and exact shortcuts. At every decision, the planner creates a fresh DAG. This prevents a counterfactual evaluation order from giving it extra refinement work. Deterministic local and static-value memo tables are shared across states within the evaluation root for work accounting; this is not a bounded physical cache or a measurement of deployment latency.

Root expansion enumerates every legal action and conditional successor. Refine the most optimistic overlapping action and its largest probability-weighted uncertain child until the node ceiling or a certificate. Select maximal lower action, quantized at 1e-12 with descending action-ID ties. If selected action a has lower L_a, then
    0 <= V*(s,b)-Q*(s,a,b) <= max_{a'} U_{a'}-L_a.
The gap certificate is approximate when the right side <=1e-10. A strictly separated real-arithmetic interval would certify a unique action; equal values can certify any optimum. The code uses double precision, tolerance and clipping, not outward-rounded verified interval arithmetic. All audit comparisons use tolerance 1e-9; observed violations at most 3.33e-16. Finite work-limit policies may select suboptimal actions, and each action's certified gap bounds its one-decision regret, not directly the full policy's value difference. By CRD-11's performance-difference identity, the trajectory sum of such bounds upper-bounds policy regret. The present receipt checks individual gaps against the oracle; it does not calculate an expected trajectory-sum bound.

## Standard benchmark
128 fresh roots 2120001..2120128, 3 branches, 1..3 mandatory sensors, budget6, cap1/2. Receding1/2 from CRD-14, sensor/local/frozen recurrent from CRD-11, full exact DP. No retraining.
| Policy | cap1 expected success | cap2 expected success |
|---|---:|---:|
| Optimal | .756401153 | .759488873 |
| Receding1 | .730662487 | .739799188 |
| Receding2 | .755983092 | .758348253 |
| Sensor-aware | .669654895 | .682681898 |
| Local DP heuristic | .701904382 | .722278713 |
| Frozen recurrent | .696696099 | .725101472 |
| Selective4 | .739589632 | .745324460 |
| Selective16 | .755626355 | .754881238 |
| Selective64 | .756401153 | .759431033 |
| Unlimited | .756401153 | .759488873 |

Primary standard cap2: selective16 vs receding2 difference -.00346702 (minus .34670 percentage points), paired descriptive 95% bootstrap [-.00586486,-.00146018], wins/losses/ties 12/22/94. Against optimum -.00460763 [-.00689025,-.00260083], 0/33/95. Against selective4 +.00955678 [.00582956,.01348651], 52/9/67. Selective64's mean regret .0000578399 (0.005784 pp); selective64 cap1 matches optimal root utility despite 44 uncertified decisions in its evaluated policy tree. Unlimited matches exact optimum on every root (up to tolerance) and certifies all reached decisions, with ties allowed. Equal value does not imply equal policy/action costs. Primary cap2 expected environment calls: selective4 4.87100, selective16 4.99868, selective64 5.02788, unlimited 5.02176, receding2 4.98661, optimal 5.01526. These are expected finite-model actions, not actual certificate-verifier calls.

| Standard cap2 | Selective4 | Selective16 | Selective64 | Unlimited |
|---|---:|---:|---:|---:|
| Evaluated decisions | 3415 | 3592 | 3605 | 3593 |
| Certified | 2576 | 3114 | 3454 | 3593 |
| Cert rate | 75.43% | 86.69% | 95.81% | 100% |
| Mean planning expansions/decision | 1.915 | 3.959 | 7.452 | 10.213 |
| Mean gap (unweighted state mean) | .0305126 | .0118717 | .0028100 | ~0 |
| Peak per-decision DAG entries | 36 | 109 | 309 | 881 |
| Allocation combinations | 339633 | 513795 | 750768 | 844398 |
| Planning outcome scores | 44096 | 103509 | 205685 | 288623 |
| Bellman backups | 10772 | 35114 | 95014 | 163318 |

Receding2 uses 635,913 allocation combinations and 102,888 lookahead outcome scores (81,260 first-backup plus 21,628 second-backup), versus selective16 513,795 (-19.20%) and 103,509 (+0.60%) respectively. Selective16 also incurs 35,114 backups and 20,894 ancestor propagations; these are additional work counters, not the same units as allocation combinations. Selective64/unlimited use more allocation combinations than receding2. Full exact DP has 86,176 policy-evaluation states and 520,378 outcome transitions for this primary cohort; selective unlimited has 3,641 policy-evaluation states plus 36,697 planning node expansions, 136,188 node creations and 288,623 planning outcome scores, fresh DAGs per decision. Do not conflate these different costs or infer total FLOPs. Counts aggregate all positive-probability evaluation histories per root, not weighted single trajectories; local formula memoization reused across those histories.

## Deeper stress
64 fresh roots 2130001..2130064, 3 branches with 1..4 sensors, budget8, cap2. Stage>=2 repeats the third predicate, as registered; this is a depth stress within a small finite state model, not a real proof problem.
| Policy | Expected success | Mean regret |
|---|---:|---:|
| Optimal | .811174293 | 0 |
| Receding1 | .793056963 | .018117330 |
| Receding2 | .808704540 | .002469753 |
| Sensor | .742925901 | .068248392 |
| Local | .782461613 | .028712680 |
| Frozen recurrent | .784026104 | .027148189 |
| Selective4 | .794457053 | .016717240 |
| Selective16 | .803604476 | .007569817 |
| Selective64 | .809410732 | .001763561 |
| Unlimited | .811174293 | ~0 |

Selective16 vs receding2 -.00510006 (minus .5100 pp), bootstrap [-.00762045,-.00294942], 7/30/27. Selective64 vs receding2 +.00070619 (plus .0706 pp), interval [-.00044402,.00190436], 18/8/38, no established gain. Selective64 mean regret .17636 pp; 50/64 roots match optimum, 14 below. Unlimited certifies every reached decision and matches optimum. Cert rates selective4 3307/4363 (75.80%), selective16 3811/4406 (86.50%), selective64 4327/4601 (94.04%), unlimited 4764/4764. Peak DAG entries 37/112/358/3983, respectively. Allocation combinations 492,516 / 680,529 / 1,242,549 / 1,920,090 versus receding2 991,311. At 16-node cap, allocation combinations decline by 31.35% relative to receding2 while utility declines. Full oracle 162,889 states, 975,141 transitions; unlimited selective 83,552 planning expansions, 625,959 planning outcomes, 596,174 backups. No controlled latency/RSS or end-to-end compute gain established. Root bootstrap intervals 2000 resamples, descriptive and unadjusted.

## Verification and scope
3,200 policy/root/cap/budget expectation evaluations (standard 2560, stress 640). 43,059 reached-state interval and selected-action regret checks, 129,837 oracle Q interval comparisons; 38,883 numerically certified decisions. Maximum numerical interval violation 3.3306690738754696e-16. The maximum actual one-step regret among finite-ceiling decisions is .13870554 (not a uniform low-regret result). Unlimited exact policy matches on all 320 root/cap combinations. Oracle action comparisons align each independent intern table by sensor stage and exact integer posterior weights; no hidden-state leakage into planning. Sixteen independent latent-world replays on first four standard roots per cap for selective16/unlimited, 3,456 worlds, max error 7.77e-16. Stress depth4 not independently world-replayed because frozen helper covers three predicates, as registered; all stress actions checked against exact recursive oracle. Both receipts parsed after commit. Source-body execution in JS isolate 25.256s / 29.049s including all controls, generation and audits. No actual verifier or physical episodes, measured CPU/RSS, standalone Node invocation, Lean kernel check or direct Cogentic proof audit.

Reproduce from repository root:
    node research/certified_recursive_descent/selective_bellman.mjs
    node research/certified_recursive_descent/selective_bellman.mjs --stress

## CRD-16 proposal (unregistered)
The important bottleneck is the repeated global allocation work and transposition graphs. Exploit independent-branch exchangeability: for any permutation of complete public branch continuation descriptors (normalized belief, remaining predicates/accuracies, active/abandoned status), simultaneously permute branch actions and eviction indices. Transition probabilities, legality, budget and terminal reward are preserved, so exact V is invariant by Bellman induction and action values correspond equivariantly. Canonicalize equivalent belief multisets, keep a reversible branch-index mapping for execution, and account for ties separately. Combine with sparse local options (zero, each affordable number of probes), Pareto-pruned min-product convolution, and a persistent DAG reused along the actual observed trajectory under a total expansion ceiling. Do not share refinement between counterfactual sibling evaluations unless the policy explicitly carries that state and work charge. Test matched total planning budgets, peak cache occupancy and measured wall time if available, against exact DP, CRD-14 receding2 and CRD-15 fresh-DAG baselines. Consider a learned proposal only with a matched classical control and safe interval fallback. Independent-branch symmetry is insufficient for correlated candidates; any correlated extension needs CRD-09 messages and a separately justified quotient. No result about integer factoring or ECDLP follows.
