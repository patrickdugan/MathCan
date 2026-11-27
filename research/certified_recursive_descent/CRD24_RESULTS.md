# CRD-24 | Shared min-product allocation factors
2026-11-27. Prospective protocol 4eba6b3e390042b1265529524010b76fedf13ee3. Source fc269b97e5743c629f11a8b3d65e82b2cec63283 (blob 3ce839e13a4bf3e03b3bd4dcb4a676706a09cb37). Main receipts standard 44362cecc5376a26d6826bbe993a309d72b46cf7 (blob b709e85191d253b82bd40d76c21cc9d58274aa10), population e140c3ce4e3c927b08a0db53ad74db25911a3585 (blob 707f253ccedd33c8e4617fbb729c2c789ccf8aa9), larger 51968c04ae022a902975d797ed92fbffc0fe62cc (blob 716c68d1f8d01e4e8075f3ec81e114c53c7c1253). Supplemental eviction diagnostic protocol 44ef892626a31614615efb34167509dffe2a036c, import guard/export 89518e8b1c65189a4ec14ed8de2c560bce40196f, source ebbb94209f78fc195fc5d44bf6f88cd45140908f (blob 10edccf1c595b3e35795d2401ffef89a570867d7), receipt 47552acdf4c69ae0e05310fa3a774736c1147652 (blob c6c706976a58b41cb307c3afa8c390ce176fa220). All four receipts parsed on readback. No fitting or policy changes after evaluation. Draft PR #291. Main shared-vector work and policy hypotheses unsupported against strong scalar/direct baselines. Tree reduces some arithmetic and beats fold at larger population on fixed traces; metadata-proxy operations, coefficient movement and cache evictions offset arithmetic savings. Exact equivalence passes, including eviction-specific diagnostic.

## 1. Algebra
For independent branch continuation descriptors in the CRD-11/14 model, let V_i(r) be optimal local success using at most r further environment actions, including mandatory sensors. Write f_i(r)=1-V_i(r). All f_i are nonnegative, nonincreasing, f_i(0)=1. For nonnegative vectors truncated to B define
    (f*g)(r) = min_{0<=t<=r} f(r-t)g(t).
Both associative parenthesizations are min_{x+y+z=r} f(x)g(y)h(z), using monotonic multiplication by a nonnegative factor. Commutativity follows by exchanging summands. The all-ones vector acts as identity on nonincreasing at-most-budget vectors because min_{0<=t<=r} f(t)=f(r). For an exact-budget coefficient convention the usual identity would instead be 1 at zero and infinity at positive costs; this experiment uses at-most vectors only. Convolution preserves nonincreasing failure with r. For any fixed independent static allocation, total failure is a product of local failures. Slack can be assigned to any component without requiring expenditure, so the minimum over allocations of total cap r returns the same best at-most-r plan. Thus
    F(s,b) = 1-(f_1*...*f_n)(b).
CRD-14's executable witness argument gives F<=V* under the original capacity/abandonment semantics. The factorization does not apply to correlated hidden states or an arbitrary adaptive policy.

If g(t)=g(t0) for a cheaper breakpoint t0<=t, then f(r-t0)<=f(r-t), and the candidate at t is dominated by t0. Keep zero and all strict decreases. Swap operands to evaluate the smaller support. Dead or unaffordable factors are all ones; neutral factors may be omitted. A local branch in this model has at most three feasible terminal probes and mandatory m sensors, so its support has at most four entries (0,m+1,m+2,m+3, with duplicates removed). A combined vector can have up to B+1 support entries. Balanced segment trees reuse unchanged factors when a branch changes; two changed leaves on eviction require recomputing the union of their ancestor paths. This is a bound on invalidated tree nodes, not on measured time or total work. When B is small the existing scalar sparse fold is a strong baseline. The numerical implementation clips probability values and uses prefix minima for monotonicity; support pruning uses strict decreases. Floating roundoff tolerated, no outward-rounded verification.

## 2. Allocators, memory and accounting
Direct is frozen metered sparse scalar allocator (unbounded canonical local/allocation memo); Scalar uses the same arithmetic with bounded FIFO scalar memo. Fold caches local failure vectors and complete root products; Prefix caches intermediate left-deep prefix products; Tree caches balanced contiguous-subset products; Tree16 is smaller version. All vector variants use support pruning, operand swap and neutral shortcut. Leaf vector keys canonicalize complete local continuation descriptors. Intermediate/complete vector keys use fixed indexed segment and local IDs (stable within the root); no claim of canonical quotient across branch permutations at segment level. A cached length h+1 can answer a smaller horizon by truncation. A larger horizon recomputes the vector. Exact deterministic values only; no oracle labels. Scalar and vector memo stores reset per decision in policy tests, while the existing indexed graph may persist along each observed path. Trace stores persist within one ordered workload.

For Scalar/Fold/Prefix/Tree/Tree2, fixed Float64Array payload is 64*(B+1)*8 bytes: 3,584 at B6, 3,072 at B5. Tree16 896/768 bytes. Scalar has 448/384 one-value slots, whereas vector modes reserve 64 records of B+1 coefficients each (including deadline scalar entries, which use a whole record). This matches typed payload, not metadata entry capacity. FIFO cache writes precharged per coefficient, evictions charged, complete values inserted atomically. Reads into separate temporary vectors charged per copied coefficient to prevent aliases after slot replacement. Computed vector initialization, segment entries, support scans and merges charged with existing proxy categories. Unbounded direct memo does not have comparable fixed numeric payload. JS Map/keys, metadata, temporary vectors, support arrays, retained graph, zeroing the allocated store, public pre-intern setup, fallback/environment execution, evaluator/oracle and other JS allocation overhead outside numeric budget and/or proxy. No physical memory or FLOP equivalence. Same per-trajectory work ceiling does not imply identical actual charged work.

Unit diagnostic same deterministic seed3050001 repeated per cohort, 256 monotone integer-vector fixtures, 1,656 coefficient checks each of associativity, identity and exact sparse-vs-dense integer product, plus 1,656 production float convolution comparisons against integer numerator/100. Three store diagnostics: horizon truncation, alias safety after FIFO eviction and atomic quota abort. All pass. Integer vectors use denominator 10 for each factor in the product tests; associativity compares unnormalized integer numerators with common denominator. These small exact checks are distinct from floating policy evaluation.

## 3. Frozen ordered successor query workload
32 standard roots 3020001..3020032, 3 branches with up to3 sensors, cap2/b6; 24 population roots 3030001..3030024, 5 branches up to2 sensors, cap2/b6; 16 larger roots 3040001..3040016, 7 branches up to2 sensors, cap2/b5. All new roots, same deterministic path order per allocator, no fitting. Query initial state at B, all nonterminal first successors at B-1 and all nonterminal second successors at B-2, retaining duplicate paths. 1,402/2,706/3,416 queries, distinct indexed counts 993/1,722/2,051. Pooled 7,524 queries (4,766 distinct within roots), 656 first and 6,796 second successor queries plus72 roots. All 7,452 transitions change one branch, because a cap2 state cannot require eviction until two branches have become active. Main trace therefore does not exercise the two-factor case; supplementary diagnostic below addresses this.

| Mode | 3-branch combinations | 3-branch work | 5-branch combinations | 5-branch work | 7-branch combinations | 7-branch work |
|---|---:|---:|---:|---:|---:|---:|
| Direct | 30670 | 61847 | 89521 | 154606 | 98346 | 175803 |
| Scalar | 30670 | 70719 | 89521 | 180187 | 98346 | 205485 |
| Fold | 19096 | 101710 | 77267 | 307974 | 113811 | 502840 |
| Prefix | 15676 | 98887 | 61032 | 326416 | 97303 | 676949 |
| Tree | 15990 | 101335 | 52246 | 283495 | 63172 | 430679 |
| Tree16 | 21979 | 184773 | 78711 | 527112 | 90506 | 742825 |

Tree vs Scalar five-branch: allocation combinations -41.64%, total work +57.33%; vs Fold total work -7.95%. Tree work exceeds Scalar on all24 roots, paired mean difference4304.50 units [4157.63,4453.46]; Tree vs Fold -1019.96 [-1158.79,-879.50], all24 lower work. Seven-branch Tree vs Fold -4510.06 work per root [-4708.25,-4289.69], but Tree vs Scalar +14074.63 [13637.75,14564.38]. Standard Tree and Fold similar total work, Prefix better than Fold; direct/scalar lower than every vector implementation. Paired root bootstrap2000 resamples, descriptive/unadjusted. Here bootstrap "wins" in the receipt counts positive numeric work differences, not favorable work outcomes. No timing claim.

Pooled over all trace cohorts:
| Mode | Work | Allocation combinations | Likelihood products | Copied read coeffs | Written coeffs | FIFO evictions |
|---|---:|---:|---:|---:|---:|---:|
| Direct | 392256 | 218537 | 20412 | 0 | 0 | 0 |
| Scalar | 456391 | 218537 | 20412 | 52754 | 11381 | 0 |
| Fold | 912524 | 210174 | 55380 | 135081 | 49356 | 5364 |
| Prefix | 1102252 | 174011 | 126600 | 92372 | 141534 | 24926 |
| Tree | 815509 | 131408 | 91740 | 73968 | 102702 | 15845 |
| Tree16 | 1454710 | 191196 | 318300 | 55705 | 191895 | 39330 |

Direct to Tree saves39.87% convolution combinations, while increasing charged work by about108%. Scalar arithmetic identical to Direct in this trace; scalar store max occupancy298 below its capacity and zero evictions. Vector records compete with leaf storage, producing recomputation (Tree likelihood91740 vs Direct20412). Five-branch Tree internal segment hits3262, root hits383, leaf hits1951; 4921 evictions; 40838 support reads and36049 coefficient writes. Seven Tree internal hits5680 but10716 evictions; Prefix18484 evictions. Tree16 worsens cache pressure and total work. Typed arrays and support/copy accounting do not provide a total byte or runtime measurement. The exact model oracle is excluded from work.

All 45,144 main value comparisons agree with independent dense AllocationProblem; 13,216 additional vector-coefficient comparisons on the first two roots per cohort. Max discrepancy1.11e-16. This checks finite static values, not optimal global policy or original factorization.

## 4. Metered closed-loop policy
Same 72 registered roots and environment models, fixed total path work2000/8000, per-decision min(R,ceil(2R/b)), pre-intern setup and original cheap/fallback. Scalar/Fold/Prefix/Tree/Tree16 substitute only allocation/local/deadline memo implementation into frozen Inc19 incCheap planner. Tree2 substitutes Tree allocator in frozen Two19. No H2 reservation or new cost gate; that decision was specified before execution to isolate allocation factors. IncCheap/Metered2 frozen controls; unrestricted exact and receding2 references. All values exact finite-model expectations up to double precision, not sampled binary trials.

| Cohort/ceiling | IncCheap | Metered2 | Scalar | Fold | Prefix | Tree | Tree16 | Tree2 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 / 2k | .663622 | .660308 | .663587 | .653545 | .653545 | .653545 | .653545 | .637881 |
| 3 / 8k | .711836 | .722674 | .711836 | .710604 | .710713 | .710175 | .706280 | .717490 |
| 5 / 2k | .745981 | .747341 | .745774 | .744257 | .744257 | .744257 | .744257 | .742579 |
| 5 / 8k | .834049 | .788190 | .832918 | .796425 | .803914 | .811600 | .789890 | .760751 |
| 7 / 2k | .698909 | .698625 | .698909 | .697595 | .697595 | .697595 | .697595 | .697076 |
| 7 / 8k | .794125 | .740867 | .791044 | .740867 | .740867 | .740867 | .732372 | .709397 |

Unrestricted exact/receding2 means 3: .72403599/.72267399, 5: .85090628/.84984320, 7: .82500072/.82304832. The seven-branch horizon shorter by design; cross-cohort rates do not establish a controlled scaling curve.

Primary five-branch 8k Tree vs Scalar -.02131825 (-2.132 pp), descriptive paired interval [-.04002019,-.00598910], 3 wins/8 losses/13 ties. Vs IncCheap -.02244885 [-.04259204,-.00746261], 2/10/12. Vs Fold +.01517484 [-.01035247,.04417286], 7/9/8; no established policy advantage. Scalar vs IncCheap -.00113060 [-.00251662,0], 0/3/21. Seven 8k Tree vs Scalar -.05017720 [-.10041022,-.00378987]; vs IncCheap -.05325783 [-.10626189,-.00763677]. Standard 8k Tree vs Scalar -.00166081 [-.00558098,.00192351], no established difference. Tree2 vs Metered2 five -.02743880 [-.04821187,-.01005405], seven -.03147034 [-.05089519,-.01471894], standard -.00518446 [-.01186230,-.00014222]. Smaller Tree16 at 8k generally worse; standard difference -.00389463 [-.00721928,-.00095061]; five interval crosses zero. 2000 paired root resamples, descriptive/unadjusted. Primary hypotheses fail, no tuned replacement selected.

Expected charged work per realized trajectory, five-branch8k:
| Mode | Total | Allocation combinations | Likelihood products | Read coeffs | Write coeffs | Support reads | New expansions | Cert rate |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| IncCheap | 6806.32 | 2374.47 | 563.90 | 0 | 0 | 0 | 4.470 | 31.22% |
| Scalar | 6814.28 | 2136.26 | 574.10 | 391.06 | 227.22 | 0 | 3.825 | 29.07% |
| Fold | 6896.35 | 1148.82 | 576.84 | 605.24 | 428.21 | 1046.69 | 1.027 | 22.74% |
| Prefix | 6779.34 | 888.83 | 586.10 | 437.01 | 765.99 | 792.04 | 2.156 | 21.90% |
| Tree | 6866.60 | 866.18 | 577.48 | 423.19 | 749.71 | 739.60 | 2.652 | 23.74% |
| Tree16 | 6941.34 | 750.95 | 1156.77 | 227.45 | 789.24 | 649.82 | .506 | 20.26% |

Tree vs Scalar fewer allocation candidates but fewer completed expansions; per-trajectory segment construction charges468.60 for Tree, plus vector initialization/copy work. Tree16 averages125.98 evictions, over twice Scalar's likelihood products. Tree5 8k fallback1.75%, Scalar .071%, IncCheap zero. Peak admitted memo records Scalar83, Tree61, Tree16 16; graph peak nodes38/21/19, IncCheap42. At seven8k Tree expands .339 vs Scalar3.012, expected charged work7228.37 vs6959.05. Tree2 also spends substantial time moving intermediate vectors. Work units are different operation categories weighted one, not measured CPU. These are descriptive costs on realized policy paths, not a causal fixed-state decomposition.

## 5. CRD-24E two-factor diagnostic
The main depth-two trace cannot reach eviction with cap2. Supplemental protocol was registered after main results, before generating these new roots. Four fresh roots per population, seeds3060001..3060004,3060101..3060104,3060201..3060204, up to2 sensors, B6 cap2. Select first16 distinct saturated reachable depth-two states with a legal eviction per root (or fewer), query each parent at b4 and all nonterminal eviction outcomes at b3. Explicitly check that the opened branch and the evicted branch both change. 176 sampled parents, 2240 genuine two-factor changes, 2416 total queries across 12 new roots. All 14496 value comparisons and39360 vector-coefficient comparisons agree with dense reference, max error1.11e-16. Separate targeted trace, not a policy or representative distribution test.

| Population | Parent states | Two-factor changes | Direct work | Scalar work | Fold work | Tree work |
|---|---:|---:|---:|---:|---:|---:|
| 3 | 48 | 192 | 4908 | 5772 | 8226 | 8146 |
| 5 | 64 | 768 | 22812 | 26860 | 52708 | 51850 |
| 7 | 64 | 1280 | 50391 | 58947 | 144469 | 168663 |

Tree reduces five-branch convolution candidates12932 to7829; seven28912 to23889. Total work still higher than scalar, seven tree also higher than fold on this selected saturated-state trace. Two-change correctness verified; no saving guarantee inferred. All four receipts parsed on readback.

## 6. Verification and limitations
72 main roots, 1152 metered root-policy expectations +144 unrestricted exact/receding2 =1296. Exact oracle204525 states,32069 offline decision visits,118823 Q interval comparisons at completed rankings,14251 certified visits. All selected regret checks, performance-difference telescoping, cumulative gap bounds, action budgets and max charged path<=2000/8000 pass. Max numerical interval violation2.22e-16, gap violation zero. Main allocation value+coefficient checks45144+13216; supplemental14496+39360. All store caps pass; maximum policy scalar occupied115, vector64, smaller16. Common public pre-intern setup standard1878 states/5818 outcomes, five1952/6096, seven1770/5547 per arm. JS source-body execution10.028/12.762/9.948 seconds includes all model generation, oracles, trace tests and audits; no controlled timing. Standalone Node/Rust CLI, hosted checks of latest draft, formal outward rounding, total memory/RSS, Lean, original Cogentic proof audit, correlated inference and real verifier/full BPD integration remain outstanding. No factoring or ECDLP result.

Reproduce:
    node research/certified_recursive_descent/shared_allocation_factors.mjs
    node research/certified_recursive_descent/shared_allocation_factors.mjs --population
    node research/certified_recursive_descent/shared_allocation_factors.mjs --larger
    node research/certified_recursive_descent/shared_allocation_eviction.mjs

## 7. CRD-25 proposal (unregistered)
Represent each factor by Pareto breakpoints (cost,failure), rather than B+1 dense coefficients. For two supports S,T, enumerate pairs (x+y, f(x)g(y)) with x+y<=B, take min product at each cost and discard any point dominated by a cheaper cost. This is exact by monotonicity of nonnegative multiplication and at-most budget. For k,l support sizes, candidate count <=kl before affordability pruning; choose between sparse pair enumeration and dense one-sided support convolution by a deterministic operation-cost rule. A local leaf has <=4 support entries; larger products can grow to B+1. This can reduce coefficient movement and repeated support scans, and allows a packed bounded numeric store with slot reuse; charge actual reads/writes and safe temporary storage. Add an expansion-local factor-reuse control (shared sibling products, then discard) before a global persistent memo; prioritize leaf values separately from product records to avoid competition. Test exact trace agreement and matched policy work against the now-strong Scalar/IncCheap baseline on fresh 3/5/7 roots and depth-three eviction paths. A fixed H2 gate remains deferred until factor work is demonstrably affordable. No learned allocator or number-theoretic result inferred.
