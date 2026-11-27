# CRD-27 | Linear admission and terminal-budget scalar allocation
2026-11-27. Prospective protocol c868fe53ade114edff90894672df901c29afc0f8. Source commit 887bb4bcfa971c2801957bdf55f3f196ad546afd (blob 76b8d8acdbac202fdca554b7ff056491d164651d). CRD-26 import-only guard e3c8182bcae2f40fe6583c30d087206beebc70d7 (blob 00ca21fd97b3a82520ddeecabb26a0a2edd4806c). Standard receipt 99a59bd42711b0c36f061f9b78bba77ced921b9e (blob 983529ff269840693a1b167b1ce1780ef03759b2); five-branch f105d3220c8835688a5c8915f45a8de802d0b6de (blob d6b88cc1958a65e378e35ce44e18976b30bc183b); seven-branch a0a5f6f94fcdfa20879971c890da825ba0dc43b1 (blob a5ef26f4cbeac033b57bdae90911789d5b10162b). All three receipts read back and parsed. No fitting or post-test tuning. Continues draft PR #291.

## 1. Exact arithmetic
Use CRD-26's joint local likelihood sweep for simultaneously requested top1/top2 values, retain strict positive local improvements with the inherited 1e-15 tolerance, and omit neutral factors. Each branch's option set O_i contains (0,0) and affordable retained (cost,success) pairs. The independent static allocation failure recursion is
    D_0(r)=1,
    D_i(r)=min_{(t,v) in O_i, t<=r} (1-v) D_(i-1)(r-t).
The desired static success is 1-D_n(b). Fused evaluates the full sparse fold after skipping neutral factors (single-factor maximum and empty zero shortcuts included). Last evaluates all coefficients for factors 1..n-1 and only r=b for the final factor. No other final coefficient can influence the returned scalar; this removes exactly the candidate evaluations for r<b at the last stage, with no changes to the other stages. The kernel's candidate cost is
    D_est = sum_(i<n) sum_(t,v in O_i) (b-t+1) + |O_n|.
This is an exact count under the registered per-candidate meter, excluding setup and option construction. The option order remains canonical by full continuation descriptor. The scalar value is cached under the inherited complete canonical allocation key, not a whole vector. CRD-14's executable static witness gives the original adaptive optimum lower bound. No correlated-branch or optional-sensor extension.

For positive factors let c_i be their smallest retained positive cost. Keep the three smallest with a single linear scan (missing entries infinity). If c_1+c_2>b, at most one positive factor fits, so take the best single value. If c_1+c_2+c_3>b, at most two can fit. Equality does not exclude the corresponding cardinality. With k_i positive options, the direct pair-loop upper charge is
    P_est = n+n(n-1)/2+ (sum_i k_i)^2 - sum_i k_i^2.
The first n charges cover single values, the next term visits every distinct branch pair, and the final term upper-bounds affordability checks and product evaluations for all positive option pairs. This is O(n) to estimate after one pass over the options, unlike the former quadratic gate. Linear admits this kernel only when its bound plus completed gate charges fits the terminal fold candidate count. Single-factor shortcut is used whenever its cardinality certificate applies, even if its gate has already consumed more than would be recovered. Table additionally considers the top-two kernel below.

## 2. Top-two distinct-branch table
For each budget r, let f_i(r) be the failure associated with the best affordable single-branch retained option. Build a table of the two smallest f_i(r) among distinct branches, keeping their branch IDs. Missing entries use the neutral failure 1 and ID -1. The best option from a branch at r can be maintained by moving its monotone option cursor as r increases. A single branch contributes at most one entry to each budget's table. Ties use smaller branch index. For every positive option (t,v) on branch i, select the first table entry at r=b-t unless its ID is i, in which case select the second. Multiplying (1-v) by that failure gives the best plan containing that specific positive option and at most one other branch. The neutral choice covers a singleton. Take the minimum of these products and 1. When the cardinality certificate excludes three positive branches, this evaluates every feasible single or pair optimum: for any optimal pair, one member is enumerated and the best distinct partner is at least as good as its actual partner. Every chosen table pair is feasible, proving equality. The result can be used with a smaller population or budget without changing correctness. It cannot replace a full fold when three positive branches may fit.

With n positive branches and K=sum_i k_i, the declared table upper work is 4(b+1)+n(b+1)+2K: four initialized scalar fields per budget, one cell scan per branch/budget, at most K cursor advances and K product evaluations. Actual temporary Float64Array has four fields per budget, i.e. 32(b+1) bytes, excluded from the persistent memo payload. The gate compares this bound with direct pair and terminal fold estimates, accounting for its own measured charges. The code takes the table only if its bound is strictly smaller than pair and fits the fold count with gate cost; otherwise pair may be chosen if it fits. At this short horizon neither kernel is selected in measured trace or policy runs. Their correctness is tested by separate forced-kernel audits. No performance or deployment advantage of the top-two kernel established on the registered population.

## 3. Numeric payload and accounting
All bounded allocators reuse CRD-24's scalar FIFO with 64*(B+1) Float64 slots, 3584 bytes at B6 and 3072 at B5. Complete local, allocation and deadline scalar keys share the same store. Direct and frozen IncCheap/Metered2 have unbounded memo payload. Local joint calculation and skip policy unchanged from CRD-26 except fusion into a single scalar allocation kernel. No new global factor vectors, no persistent value cache across decisions, no H2 reservation or learned gate. Policy graph copy on actual observed path follows frozen Inc19. Metadata, temporary DP/table arrays, graph, public model tables, sorting and JS allocator overhead, fallback/environment execution and evaluator/oracle outside the declared payload and/or work proxy. Equal numeric payload does not guarantee equal physical memory. All recorded units are the previous weighted operation ledger, not measured FLOPs or CPU cycles. Abort work charged.

## 4. Frozen allocation trace
Fresh standard24 roots 3320001..3320024 (3 branches, up to3 sensors, cap2/B6), five20 roots 3330001..3330020 (up to2 sensors, cap2/B6), seven12 roots 3340001..3340012 (up to2 sensors, cap2/B5). Common ordered CRD-25 query trace includes initial, first/second nonterminal successors and actual eviction successors of first eight distinct eligible saturated depth-two parents. 2019/4365/4595 queries, pooled10979 (6177 distinct within roots). 5867 single-factor changes,4608 two-factor changes,504 initial/repeated parent queries. All modes receive identical queries; traces do not tune policy. Each result compared with independently aligned dense AllocationProblem, and first two roots/cohort separately audited at all budgets with independent caches.

| Allocator | 3-branch work | 5-branch work | 7-branch work | Pooled work | Pooled allocation combinations | Pooled likelihood products |
|---|---:|---:|---:|---:|---:|---:|
| Direct | 57026 | 187694 | 185704 | 430424 | 243406 | 17292 |
| Scalar | 65620 | 219543 | 215882 | 501045 | 243406 | 17322 |
| Joint | 62592 | 218425 | 214922 | 495939 | 243406 | 8676 |
| Skip | 64338 | 215573 | 204974 | 484885 | 227246 | 17322 |
| Both (old quadratic gate) | 64640 | 278014 | 272724 | 615378 | 186153 | 8676 |
| Fused | 61310 | 214455 | 204014 | 479779 | 227246 | 8676 |
| Last | 55369 | 201609 | 195859 | 452837 | 200304 | 8676 |
| Linear | 62364 | 244318 | 231274 | 537956 | 171463 | 8676 |
| Table | 62364 | 244318 | 231274 | 537956 | 171463 | 8676 |

Fused pooled work -4.24% vs Scalar; Last -9.62% vs Scalar and -5.62% vs Fused. Every one of the 56 fixed-trace roots has lower Fused work than Scalar and lower Last work than Fused. Last standard work -15.62% vs Scalar and slightly below Direct; Last five -8.17% and seven -9.27% vs Scalar. Pooled Last remains 5.21% more work than Direct with unbounded memo. Pooled Last convolution candidates -17.71% vs Scalar, local likelihood products -49.91%. The terminal fold itself saves 26942 candidate evaluations versus Fused, exactly the difference in pooled work. All bounded modes have40 FIFO evictions in the seven-branch trace and zero in other cohorts. No cache performance benefit inferred beyond the specified traces.

Primary five Fused vs Scalar mean paired work -254.4 units/root, descriptive 95% bootstrap [-263.05,-245]; Last vs Fused -642.3 [-675.45,-609.90]. Both differences favor the new kernel on all20 roots. Linear vs Last +2135.45 [1978.90,2285], Table vs Last +2135.45 [1985.95,2282.40], higher on all20. Linear vs old Both -1684.8 [-1797.35,-1557.55], lower on all20. Gate overhead lower than old implementation (pooled113960 charged estimator units vs173288) but still substantial. Linear/Table each 1848 single-cardinality cases,4079 two-eligible states,4079 rejected pair/table gates, zero admitted pair or table executions. Lower arithmetic candidate count does not overcome gate charges; pooled total +18.79% vs Last. Because the table and pair are never admitted, their trace equality is a shared fallback-kernel result, not evidence of equal performance when selected. The old Both does use different admission rule. Work-bootstrap wins counts positive cost difference, not favorable work outcomes. All 2000 resamples fixed per comparison, descriptive and unadjusted.

## 5. Metered closed-loop results
Frozen IncCheap and Metered2, bounded Scalar/Joint from CRD-26, Fused/Last/Linear/Table use Inc19 with changed allocation kernel; Last2 replaces allocation in Two19. Same56 fresh roots, total work2000/8000 and decision quota min(R,ceil(2R/b)), common public setup, fallback and graph copy. Exact oracle and unrestricted receding2 are nonmatched references. Conditional expected utility, not sampled binary success.

| Cohort/ceiling | IncCheap | Metered2 | Scalar | Joint | Fused | Last | Linear | Table | Last2 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 / 2k | .701933 | .696269 | .697824 | .697824 | .699912 | .701933 | .699912 | .699912 | .701918 |
| 3 / 8k | .756959 | .755310 | .756959 | .756959 | .756959 | .756959 | .756959 | .756959 | .755310 |
| 5 / 2k | .705690 | .713635 | .705690 | .705690 | .705690 | .705690 | .705690 | .705690 | .713635 |
| 5 / 8k | .788568 | .728809 | .788568 | .788568 | .788568 | .790372 | .788568 | .788568 | .729860 |
| 7 / 2k | .714722 | .712723 | .714722 | .714722 | .714722 | .714722 | .714722 | .714722 | .712723 |
| 7 / 8k | .762856 | .742985 | .762398 | .762856 | .775381 | .775381 | .758114 | .758114 | .745580 |

Exact/receding2 means standard .75765302/.75530976; five .81937781/.81795244; seven .79353700/.79223844. Seven horizon shorter by registration; values do not give controlled cross-population scaling.

Primary five8k Last vs Scalar and IncCheap both +.00180374 (+.18037 pp), descriptive paired interval [0,.00541123], 1 win/0 losses/19 ties. Table vs Last -.00180374 [-.00541123,0]. No strictly positive policy utility gain established in primary comparison. Standard2k Last vs Scalar +.00410877 [ .00041879,.00957931], 4/0/20, and ties IncCheap all24; Last2 vs Metered2 +.00564928 [.00010940,.01383193],4/0/20. At standard8k all incremental arms tie exact same root utilities; Last2 ties Metered2. Seven8k Last vs Scalar +.01298261 [0,.03894784], and vs IncCheap +.01252437 [0,.03757310], both1/0/11. Fused/Last tie on all12. Seven Table vs Last -.01726685 [-.05029726,.00955497],1/4/7, uncertain. Last2 vs Metered2 +.00105090 [0,.00273453] on five and +.00259515 [0,.00706105] on seven. No general policy advantage established, no post-test gate changes. All bootstrap intervals descriptive/unadjusted.

Five8k expected charged work per realized trajectory:
| Mode | Total work | Allocation candidates | Likelihood products | Gate work | Expansions | Certified decision rate |
|---|---:|---:|---:|---:|---:|---:|
| IncCheap | 6783.56 | 2393.19 | 521.17 | 0 | 4.217 | 27.33% |
| Scalar | 6817.95 | 2159.37 | 529.03 | 0 | 3.719 | 25.55% |
| Joint | 6817.82 | 2185.42 | 300.69 | 0 | 3.719 | 25.55% |
| Fused | 6802.44 | 2096.61 | 300.84 | 0 | 4.006 | 27.57% |
| Last | 6780.05 | 1904.62 | 297.52 | 0 | 4.365 | 28.14% |
| Linear/Table | 6803.82 | 1572.23 | 300.03 | 845.23 | 3.953 | 27.00% |
| Last2 | 6839.37 | 2217.31 | 212.31 | 0 | 0 | 16.80% |

Standard8k Last work5509.33 vs Scalar5589.10 and IncCheap5510.45, same utility. Last2 work3814.19 vs Metered2 3899.69, same utility. Seven8k Last work7227.42 vs Scalar7297.61, Fused7240.56 and IncCheap7274.58; last expands3.554 vs scalar2.570. These are probability-weighted operation counts along different realized policy paths, not a causal matched-state comparison or hardware speed measurement. Trace comparisons isolate fixed query work. Linear/Table zero pair or table executions at all policy budgets, so performance is entirely due to gate cost, single shortcut and terminal-fold fallback. Fixed scalar payload unused capacity in policy evaluations; no claim of total RAM limit.

## 6. Audits and limitations
56 fresh roots,1008 metered root-policy expectations plus112 unrestricted references=1120. 173733 exact labeled oracle states;28285 offline decision visits,110801 complete-ranking Q interval comparisons,13703 numerical certified visits. Every chosen action (including fallback) checked against oracle, max numerical interval violation3.33e-16, gap violation zero. All expected regret telescoping and cumulative bounds, environment/capacity limits, charged path ceilings2000/8000, scalar store capacities pass; policy peak129 occupied scalar slots. 98811 trace allocation checks and50265 separate all-budget checks, max1.11e-16. Same deterministic unit diagnostic per cohort: 1680 integer-numerator reference comparisons, including378 forced pair/table calls (189 each),190 table exclusion events and616 kernel cost-bound checks. Forced table with ties, budget equality, neutral/single cases passes. Repeated identical unit diagnostic not three independent campaigns. Public pre-intern setup standard1432 states/4341 outcomes, five1700/5391, seven1384/4366 per arm. Source-body executions6.856/10.319/7.075 seconds include oracle, generation and audits; not controlled timing or standalone CLI. All three receipts parsed. No physical CPU/RSS, formal outward rounding, Lean, original Cogentic factorization proof audit, actual theorem verifier, full BPD/TRM or correlated-inference result. No new factorization or ECDLP claim.

Reproduce:
    node research/certified_recursive_descent/linear_scalar_kernels.mjs
    node research/certified_recursive_descent/linear_scalar_kernels.mjs --population
    node research/certified_recursive_descent/linear_scalar_kernels.mjs --larger

## 7. CRD-28 proposal (unregistered)
Freeze Last as the simplest improved scalar kernel. Test boundary and demand pruning rather than another expensive shortcut gate. The first factor can assign its monotone best local option directly at each requested budget, since D_0(r)=1. For a fixed target b, define R_n={b} and recursively R_(i-1)={r-t:r in R_i,t in O_i,t<=r}. Computing only coefficients indexed by these demanded sets yields the exact same target by backward dependency closure and forward DP. At short horizons, small bitsets can represent demanded budgets; meter all set construction and dependency scans and compare to ordinary terminal fold. Test cheap fixed ordering by retained option count/cost (commutativity allows reordering) with order overhead charged. Include direct first-boundary plus last-boundary control and separate demanded-budget variants, strong scalar/IncCheap/Metered2 references, fresh cohorts and exact eviction checks. If demand analysis costs more than it saves, retain simple terminal scalar. No learned gate until validated; independent original proof audit and real hardware profiling still outstanding.
