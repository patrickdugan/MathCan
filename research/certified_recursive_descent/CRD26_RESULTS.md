# CRD-26 | Joint scalar likelihoods and exact affordability shortcuts
2026-11-27. Prospective protocol 8f7bda70bcd18316cf646aa2f1c1c2aaea2fb8c6. Source cc4d8e4643074361e7c29646fff53c219619b7a0, pre-execution unit-fixture correction c094a01764476e6e968a742809b3144356f36acd (blob e07a3357c7df1316d8d4a5b804cfd559f3f1e685) filters unaffordable hand-test options before invoking the shortcut kernel. CRD-25 interface-only import guard d30e2e3708fb4b738f026b610cdb360ab7a780e1 (blob beb75b6368165612307a82f3526806efecf060ca). Standard receipt 37a2394707fea536333152740a69105590ede3d1 (blob 18bed51022492c315a09fa5c45e7d4a639fce170), five-branch 2f8b6a0aade4c4b97b80ed2d8b6e4b78b0c27b5a (blob 39a41b8b7a40c4ed3159ba7e7cdedd0ac3c3c6bb), seven-branch 34cd4276a0127a7125b012926a7b5b8770e0778d (blob 77fc22a38d519d4d12ee98319e11cdbbadbe0d3a). All three receipts read back and parsed. A mistyped dependency SHA halted the first population invocation before execution; verified the exact guard blob and reran unchanged. No fitting or outcome-dependent policy changes. Draft PR #291.

## 1. Joint scalar local evaluation
Under the frozen independent finite branch model, with m remaining mandatory sensors and three disjoint feasible terminal targets, set
    w_j(u) = p_j P(u | j), j=0,1,2.
For k affordable probes after the remaining sensors, exact local V(m+k)=sum_u TopSum_k(w(u)), with V=0 for insufficient calls and V=feasible mass when k>=3. The one- and two-probe values share every likelihood multiplication. Sort each feasible-weight triple once and accumulate both sums. This is the CRD-12 local identity and CRD-25 joint sweep, now inside scalar allocation; no dense or packed global factor construction.

Joint uses a shared sweep only when both unsaturated values are requested in the current allocation and missing; if one is already cached, compute only the missing value. A local isolated query uses the frozen single-value calculation. EagerJoint also attempts the other value for a one-value request when the second cost is within the fixed root horizon, even if beyond the current request. Both use exact scalar descriptor-and-cost keys, same fixed FIFO store and local value formula. A complete individual value can be inserted before the other write; interruption leaves only valid cached values. Joint extra accumulation charged for each of the two outputs per word. No learned predictor, hidden labels or optional-sensor generalization.

## 2. Affordability shortcuts
For each live branch, retain zero and positive options at costs m+1,m+2,m+3 whose utility increases by more than the frozen 1e-15 tolerance over the cheaper retained option. Let c_i be its smallest retained positive cost; dead, unaffordable and zero-success factors are neutral. Skipping neutral factors preserves the static optimum. If at most one positive factor exists, maximize its local options. If the two smallest c_i sum to more than b, every feasible allocation has at most one positive factor. If the three smallest sum to more than b (missing entries infinity), at most two can contribute. The latter case evaluates all affordable single options and pairs of options from distinct branches. Independence gives joint failure (1-v_i)(1-v_j). The minimum failure is the exact static solution over retained options. Equality at either threshold permits the corresponding number of branches; strict comparison required. The sorted-minimum test strengthens the earlier floor(b/min c_i) bound.

These are exact real-arithmetic reductions for the nonnegative at-most-budget objective; the production support tolerance and floating arithmetic remain inherited numerical approximations. All audits compare to independent dense reference within tolerance. Short uses the single shortcut when available, otherwise estimates pair cost:
    P_est = n + sum_(i<j) [1+2 k_i k_j]
where k_i counts positive options. Sparse DP candidate count:
    D_est = sum_i sum_(t in retained options i) (b-t+1).
Only use pair enumeration when the pair estimate <= DP estimate and at most two branches can contribute. Pair estimate bounds declared pair-loop charges after admission, not all compute including the estimator. Charge each estimator scan, comparison, branch pair and option affordability test. The current implementation sorts minima and uses a quadratic loop over branch pairs for the estimate; this turns out to be the main failure mode. The gate does not account for the cost of computing the gate in advance. Skip uses the same neutral-factor omission and one-factor shortcut but ordinary sparse DP for multiple factors. Both combines Joint and Short. Joint/EagerJoint retain original canonical order and identity factors to isolate local formula fusion.

## 3. Fixed numeric store and work contract
All bounded modes share the CRD-24 scalar FIFO store of 64*(B+1) float64 slots (448/3584 bytes for B6; 384/3072 bytes for B5). Local, global allocation and deadline scalar namespaces share one capacity. No separate factor vectors, no cross-decision memo persistence. Direct trace control uses frozen unbounded memo. Each cache coefficient read/write, lookup and FIFO eviction charged as in CRD-24. JS metadata/keys, temporary DP arrays, local model tables, retained graph, allocator/object overhead, fallback/environment execution and exact evaluator/oracle excluded from typed bytes and/or planning work proxy. Policy graph retained only along actual observed successors and copied separately for counterfactual histories, with existing charges. No physical RSS or runtime comparison.

## 4. Frozen common traces
Fresh 24 standard roots 3220001..3220024 (3 branches up to3 sensors, cap2 B6), 20 five-branch roots 3230001..3230020 (up to2, cap2 B6), 12 seven-branch roots 3240001..3240012 (up to2, cap2 B5). Identical CRD-25 query generator: initial, first and second nonterminal successors, first eight distinct saturated depth-two parents and their actual nonterminal eviction outcomes. 2015/4351/4589 queries, pooled10955 (6153 distinct within roots). 5843 single-factor changes, 4608 two-factor changes, 504 initial/repeated parent queries. Every mode receives identical ordering with cache retained within root. No trace-based fitting. Audit all values against aligned dense AllocationProblem. Extra all-budget and native local DP checks on first two roots per cohort use separate caches and meters; those extra audits do not warm measured traces or enter their work.

| Mode | Three-branch work | Five-branch work | Seven-branch work | Pooled work | Pooled allocation combinations | Pooled likelihood products |
|---|---:|---:|---:|---:|---:|---:|
| Direct | 56295 | 186579 | 187918 | 430792 | 244163 | 14808 |
| Scalar | 65191 | 218504 | 218898 | 502593 | 244163 | 14856 |
| Joint | 62833 | 217476 | 217992 | 498301 | 244163 | 7452 |
| EagerJoint | 63643 | 219300 | 232368 | 515311 | 244163 | 7488 |
| Skip | 63874 | 214474 | 209002 | 487350 | 228920 | 14856 |
| Short | 70170 | 276973 | 279655 | 626798 | 189489 | 14856 |
| Both | 67812 | 275945 | 278749 | 622506 | 189489 | 7452 |

Joint halves likelihood multiplication approximately (49.84% pooled), 570 joint sweeps and 3112 charged joint output accumulations. Total work declines 0.854% vs Scalar, lower on all56 individual trace roots. Three-branch Joint vs Scalar mean -98.25 units/root [descriptive paired 95% bootstrap -119.92,-76.92], five -51.40 [-60.40,-41.50], seven -75.50 [-95,-57.5]. EagerJoint costs more than Joint in all pooled cohorts, especially seven (additional14376 units), with slightly more likelihood products and evictions. Skip removes4609 neutral factors, reduces candidates6.24% and pooled work3.03%; all56 roots lower work vs Scalar. Five Short vs Skip +3124.95 units/root [2967.5,3281.25], all20 higher. Both vs Scalar +2872.05 [2710.4,3025.45], all20 higher; all 20 higher than Joint too. Both lowers pooled candidate count22.39% relative to Scalar but work increases23.86%. Both/Short each 1636 single cases, 393 pair cases, 3809 rejected pair gates, 174670 gate-estimate units; ~90.65% of two-eligible pair gates reject. On five branches only3 pair cases against1888 rejected; seven only5 against1542. Cost estimator rather than convolution arithmetic dominates. Pooled all bounded modes except EagerJoint incur46 FIFO evictions (all in seven branch trace), EagerJoint55. Direct remains least total work with unbounded memo; comparator payload unbounded. Work bootstrap "wins" counts positive differences (more work), not favorable outcomes. All 2000 paired resamples fixed/descriptive/unadjusted.

All 76685 main allocation comparisons, 38773 separate all-budget global checks and 29211 local native-DP value checks pass. Max numerical discrepancy 2.22e-16. Deterministic unit diagnostic same seed3250001 repeated in each cohort: 256 generated integer-rational fixtures, threshold hand cases and empty/one-factor cases; 795 exact-numerator reference comparisons across Skip/Short/Both, max1.11e-16. 156 two-eligible cases,94 pairs and62 rejections within the repeated unit run; threshold equalities exercised. No formal outward rounding.

## 5. Metered closed-loop benchmark
Same 56 fresh roots; frozen IncCheap and Metered2; Scalar, Joint, EagerJoint, Skip, Short, Both as allocation/local/deadline substitutions into frozen Inc19. Both2 uses Both in frozen Two19 two-step comparator. No new gate or H2 reservation. 2k/8k total path allowances, decision quota min(R,ceil(2R/b)), common public setup/fallback and graph semantics. Unrestricted exact/receding2 references. Conditional expected success, not binary trial rates.

| Cohort/ceiling | IncCheap | Metered2 | Scalar | Joint | EagerJoint | Skip | Short | Both | Both2 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 / 2k | .704380 | .709908 | .703035 | .703035 | .703035 | .704380 | .704380 | .704380 | .710689 |
| 3 / 8k | .763865 | .770862 | .763384 | .763677 | .763213 | .763677 | .763677 | .763677 | .770862 |
| 5 / 2k | .758969 | .766383 | .758867 | .758867 | .758867 | .758969 | .758969 | .758969 | .766383 |
| 5 / 8k | .813948 | .781015 | .812444 | .812444 | .811042 | .813948 | .811920 | .811920 | .786100 |
| 7 / 2k | .706959 | .706959 | .706959 | .706959 | .706959 | .706959 | .706959 | .706959 | .706959 |
| 7 / 8k | .797533 | .726081 | .789609 | .795664 | .777311 | .789609 | .782484 | .782484 | .729329 |

Unrestricted optimum/receding2 means standard .77254762/.77086189; five .84840119/.84620628; seven .81442926/.81288927. Shorter seven horizon fixed before test; cohorts do not constitute controlled scaling curve.

Primary five 8k Both vs Scalar -.00052394 (-.05239 pp), paired descriptive interval [-.00532358,.00396260], 1 win/2 losses/17 ties; vs IncCheap -.00202734 [-.00581342,.00018237]; vs Joint -.00052394 [-.00532358,.00399669]. No utility gain established. Joint vs Scalar ties all20 five-branch roots. Skip ties IncCheap root utility on all20 by comparison of aggregate values and paired Scalar differences (utility equivalence here; no identical action tree claim). Seven Joint vs Scalar +.00605499 [-.00444003,.02367338], 1/2/9; not established. Seven Both vs Scalar -.00712512 [-.01374540,-.00155309], 0/4/8; vs Joint -.01318011 [-.02974212,-.00016079]; EagerJoint vs Joint -.01835316 [-.04459744,0]. Standard 8k Joint/Both equal policy mean .76367690; +.00029304 vs Scalar with lower bootstrap endpoint zero. Both2 standard 8k matches unrestricted receding2 mean and Metered2 up to floating arithmetic, uses more work. Five Both2 vs Metered2 +.00508527 [0,.01486983], seven +.00324729 [0,.00669872]; intervals touch zero, no strictly positive advantage established. All paired resamples descriptive and unadjusted; no tuned selection.

Expected work per realized trajectory, five-branch8k:
| Mode | Total | Allocation combinations | Likelihood products | Gate estimate work | Expansions | Certified decisions |
|---|---:|---:|---:|---:|---:|---:|
| IncCheap | 6930.64 | 2451.93 | 481.50 | 0 | 4.181 | 23.06% |
| Scalar | 6979.95 | 2215.00 | 487.82 | 0 | 3.638 | 21.35% |
| Joint | 6979.78 | 2236.39 | 276.11 | 0 | 3.660 | 22.02% |
| EagerJoint | 6990.51 | 2208.33 | 275.14 | 0 | 3.482 | 20.43% |
| Skip | 6956.96 | 2108.02 | 484.96 | 0 | 3.968 | 24.25% |
| Short | 6922.57 | 1661.15 | 496.23 | 1015.92 | 3.396 | 24.23% |
| Both | 6922.32 | 1686.36 | 278.87 | 1037.17 | 3.455 | 24.23% |
| Both2 | 7000.40 | 1638.28 | 182.62 | 1349.17 | 0 | 11.14% |

Joint lowers likelihood work43.4% vs Scalar on realized trajectories but similar total work/utility. Both rejected pair gates25.89 per path vs .940 pair executions; estimate cost~1037.17 units. Lower actual work may arise from early interruption and changed paths, not a causal fixed-state saving. Seven 8k Joint work7213.30 vs Scalar7268.18, likelihood321.88 vs543.02, success point estimate .795664 vs .789609; eager performs worse. Both's fewer arithmetic candidates do not compensate for the expensive admission loop. Standard 8k Both2 4403.64 units vs Metered2 3864.63, equal mean utility. All policy bounded stores peak121 entries (capacity448/384); no policy cache binding at these quotas. Work is an explicitly defined proxy, not physical time.

## 6. Audits and limitations
56 fresh roots,1008 metered root-policy expectations plus112 unrestricted references=1120. Exact labeled oracle162327 states;26673 offline decision visits,107595 completed-ranking Q comparisons and12554 numerical certified visits. Every chosen action including fallback checked against exact oracle; max interval discrepancy2.22e-16 and gap violation zero. All expected regret telescoping, expected cumulative bounds, environment/capacity limits, total charged ceilings (2000/8000) and scalar storage capacities passed. Public pre-intern setup standard1256 states/3856 outcomes, five1466/4591, seven1286/3983 per arm. Source-body executions5.836/10.105/6.678 seconds include traces, audit, oracle and generation; not controlled timing or standalone Node execution. All three receipts parsed on readback. No total physical memory or wall-clock measurement, formal outward rounding, Lean, original Cogentic factorization proof audit, actual theorem-verifier run, correlated inference or full BPD/TRM experiment. No number-theoretic breakthrough claimed.

Reproduce:
    node research/certified_recursive_descent/joint_scalar_allocation.mjs
    node research/certified_recursive_descent/joint_scalar_allocation.mjs --population
    node research/certified_recursive_descent/joint_scalar_allocation.mjs --larger

## 7. CRD-27 proposal (unregistered)
The fixed trace results identify Joint and Skip as low-overhead changes worth testing together without the expensive shortcut estimator. Fuse neutral-factor omission and joint local evaluation, preserving the scalar baseline. For the exact cardinality shortcut, find the three smallest retained costs in a single scan, with no sort. For k_i positive options, compute the pair upper count in O(n) using
    2 sum_(i<j) k_i k_j = (sum_i k_i)^2 - sum_i k_i^2,
    P_est = n + n(n-1)/2 + (sum_i k_i)^2 - sum_i k_i^2.
Compute D_est from the same option scan. Charge these operations and only admit a pair loop when savings cover the additional gate cost under the declared proxy. Consider an exact top-two single-branch table indexed by budget: for each r keep the smallest two failure values from distinct branches; for a pair option on i at t use the best other branch at r=b-t. This avoids quadratic branch pairing and can be compared against direct pair enumeration and the simple sparse fold. The optimum with at most two positive branches is min of all singles and all such pair products; preserve valid ties and threshold cases. Further reduce static fold work by evaluating only the final budget in the last factor instead of computing every output coefficient when callers only need F(s,b). These are exact arithmetic opportunities, not observed improvements. Register on fresh cohorts, include eviction paths and actual operation-level costs; retain IncCheap, bounded scalar and Metered2 references. No H2 gate or learned allocator until simple kernel cost is validated. Controlled standalone Node/Rust and original Cogentic/Lean proof audit remain separate outstanding work.
