# CRD-13 | Sufficient-statistic compression and certified local likelihood bounds
2026-11-27. Extension of CRD-12 in PR #291, still draft. Three prospective subcampaigns; B/C were registered after previous subcampaign outcomes and before new roots. A protocol e597a7d740f357b1f49d0b453ecbd01b517f596f, source c04e3040b947ed736f194acdb5c633aab055d7db, receipt 1f82e4fbae81bb5af2ceaaeb55da4ac0fa8a114c. B protocol b8a779181dec61a4d756a34ff1b78d91f5f11180, denominator correction 519d38eade17f61086ecec3a51a6de0d58381f41 before generating data, source 459f08c4a8df6c282883ba7a328fff7feae792a8, receipt b9bc45484298f6f7334934a8af99c3120134fc8a. C protocol b69f033ab72563c69806b65ca48bd5f0eb4ecec1, source e060927d20db969a1e430360e0e1765543da0cec, receipt 3f0c5fd33dabaf3d696cd06de74fa3ed9b4e8cbe. No trained model in this study. Independent mandatory binary sensors, three mutually exclusive feasible terminal states, unit probe costs. No result about original Cogentic factoring theorem, arbitrary correlated hypotheses, or full BPD/TRM.

## Exact compressed likelihood
For state i and a family of n sensors with common predicted bit z_i and reliability a/d (q=d-a), count h positive observations. The integer likelihood factor is binom(n,h) a^h q^(n-h) for z_i=1 and binom(n,h) q^h a^(n-h) otherwise. Every likelihood sum over h equals d^n. By positive homogeneity of TopSum_k, each count cell can aggregate all equal-likelihood bit words before taking top-k. Complementing a predicate and flipping its observed bit preserves the summed utility; reduce reliability rational and canonicalize masks. Any sensor with a constant predicate across feasible states or a/d=1/2 multiplies all feasible-state masses by a common scalar. Summing that scalar over outcomes gives one, even if the sensor distinguishes infeasible states. This uses cancellation of posterior normalization from CRD-12; it is not a statement that such sensors have no information about the full six-state posterior.

With grouped counts the cardinality is product_g(n_g+1) rather than 2^m, polynomial in m for fixed number of distinct sensor types but still exponential when every sensor has a distinct type. All computation uses exact BigInt numerator/denominator. Original raw bit recursion retains all sensors and uses original mask and accuracy; cross-multiplied fractions must agree.

At a prefix with integer masses w_i, denominator D of remaining groups, let S be current top-k. Lower L=D TopSum_k(w) corresponds to ignoring remaining observations; upper U=D sum_i w_i corresponds to probing all feasible states. If for each i in S and j outside S,
    w_i product_{remaining differing predicates} min(a,d-a)^n >=
    w_j product_{remaining differing predicates} max(a,d-a)^n,
then for every completion the same S is optimal. Common likelihood factors, including zero factors, preserve the inequality. Sum all remaining words at once, giving exact L. This is sufficient, not necessary. Best-first maintains a disjoint prefix partition and integer sums of lower/upper contributions; chooses largest unresolved gap (insertion tie). A finite expansion budget returns exact enclosure, not necessarily exact value.

## A: frozen checks and work
140 roots, 66 raw rational equality checks, 124 exact grouped/pruned equality and k-monotonicity checks, 76 bounded roots. On small 64 roots unpruned grouped visited 6,159 nodes vs pruned 906. Repeated 128-sensor regime max grouped cardinality 106 (12 roots), mean 31.9167 discarded sensors. At 36 sensors balanced six-family mixture, max grouped outcomes 117,649 vs raw 68,719,476,736; across eight roots unpruned 1,098,056 nodes vs pruned 275,794, a 74.88% reduction. At unique reliability depth16 unpruned 1,048,568 nodes vs 204,114, a 80.53% reduction. These are node counts, not measured speedups.

| A mean interval width (probability units) | 0 expansions | 32 | 128 | 512 |
|---|---:|---:|---:|---:|
| Mixed 24 | .140388 | .00992685 | .00541601 | .000448662 |
| Mixed 36 | .153935 | .00430719 | .00312280 | .00140460 |
| Unique 16 | .163352 | .00366058 | .00125909 | .000510880 |
| Unique 32 | .159172 | .000891189 | .000150707 | .0000255310 |
| Unique 64 | .170134 | .000228422 | .0000197277 | .00000160388 |

Repeated groups solved exactly in one internal group expansion (which creates n+1 count children). All reference values contained at every checked step; nestedness and integer range checks passed. Depth32/64 unique no exhaustive reference, so correctness there follows from the bound proof and implementation checks, not independent exact-value reproduction. These unique fixtures have reliability (d-1)/d with increasing d, hence high information at large depth. Their narrow intervals are not representative of weak or moderate sensors. A mean/max widths are decimal display of exact rational widths; receipts keep full numerator/denominator strings. BigInt bit lengths and generated nodes are logged; memory overhead unmeasured. A elapsed 4.293s in JS isolate, not controlled benchmark.

## B: total-variation upper bound
Write p_i(u) for remaining outcome probability and x_i=w_i p_i(u). For any top-k set T(u), relative to fixed current top-k S, pair elements of T minus S with S minus T. The improvement is at most sum over all cross pairs (x_j-x_i)_+. Since w_i>=w_j, each such term <= w_j (p_j-p_i)_+. Summing over words yields
    V <= TopSum_k(w) + sum_{i in S,j not in S} w_j TV(P_i,P_j).
Units here exclude D; multiply by D to get numerator bound. For independent Bernoulli outcomes with a+q=d, differing predicates give 1+chi^2(P_j||P_i)=1+(a-q)^2/(a q), while equal predictions contribute factor one. Across sensors multiply factors. If q=0 on a differing prediction, use TV<=1. Cauchy-Schwarz gives TV<=min(1, sqrt(chi^2)/2). A second bound uses uniform reference U: top-k gain over fixed top-k w times U <= sum_i w_i (P_i-U)_+ at each word, and sum gives sum_i w_i TV(P_i,U). Uniform chi-square multiplier 2(a^2+q^2)/d^2, independent of predicted bit. Use the minimum of upper bounds including original U. Convert rational radicands to ceiling integers and verify integer square root by (r-1)^2<n<=r^2. Bounds exact, may be loose. Group count words are sufficient; raw-bit overlap/TV bounds remain valid after coarsening. Combined frontier upper may increase after a split because the local relaxation changes; publish intersection of successive valid global intervals.

48 new roots, 16 exact raw/grouped references (depth12), no exact reference at depths32/64. Weak reliability (d+1)/(2d), odd d=21+2t; moderate reliability (2d+1)/(3d), d=10+3t. Protocol initially stated d=11+3t, corrected before data generation to make numerator integral and reduced. Priors deliberately near-balanced on feasible states. At 512 expansions, mean widths:
| Regime/depth | Original | TV |
|---|---:|---:|
| Weak 12 | .0519184 | .00201677 |
| Weak 32 | .291420 | .0264983 |
| Weak 64 | .292722 | .0314386 |
| Moderate 12 | .0646657 | .0410733 |
| Moderate 32 | .102744 | .102744 |
| Moderate 64 | .0973627 | .0973627 |

TV substantially improves weak case but is vacuous for moderate deep fixture. At weak64 width still 3.14386 percentage points. At moderate32/64 all original and TV outcomes exactly tie because the product divergence upper is too large. No zero-width certificates at 512 in these fixtures. Exact depth12 values contained. B elapsed .953s in JS isolate; no runtime comparison.

## C: likelihood-overlap lower bound
For k=1, error relative to all feasible mass is sum(x)-max(x), which is <= sum over unordered pairs min(x_i,x_j). For k=2, error min(x) <= min(x_i,x_j) for any pair. Since min(x,y)<=sqrt(xy),
    V_1 >= sum_i w_i - sum_{i<j} sqrt(w_i w_j) B_ij,
    V_2 >= sum_i w_i - min_{i<j} sqrt(w_i w_j) B_ij,
where B_ij=sum_u sqrt(P_i(u)P_j(u)) is the Bhattacharyya affinity. Conditional independence factorizes B: shared predictions contribute 1; distinct predictions contribute 2 sqrt(a q)/d. In numerator units, D sqrt(w_i w_j) B_ij is square root of integer w_i w_j times product of d^2 (same) or 4a q (different), each to appropriate group count. Ceiling integer square root overestimates error, hence preserves valid lower bound. Max with original L and min with B upper. Exact ranking certificates still take precedence. No learned error model or floating-point rounding assumption needed. Both upper and lower envelopes support arbitrary feasible weights, including zeros. Moderate signal exposes the complementarity: TV bounds can be loose when likelihoods separate, while affinity is small. Affinity lower bound can itself be vacuous at weak signal.

72 new roots across weak, moderate and high regimes. 24 exact depth12 raw/grouped reference comparisons; all bounds contain exact references. Depth32/64 no exhaustive reference. All BigInt interval validity and nested intersection checks pass. Mean widths in probability units:
| C regime/depth | Original (512) | TV (512) | Combined (0) | Combined (512) |
|---|---:|---:|---:|---:|
| Weak 12 | .0954889 | .00363925 | .0376826 | .00363880 |
| Weak 32 | .250601 | .0215098 | .0380746 | .0215052 |
| Weak 64 | .262224 | .0271943 | .0428705 | .0271890 |
| Moderate 12 | .0672539 | .0429382 | .228652 | .0427059 |
| Moderate 32 | .109075 | .109075 | .106101 | .0846638 |
| Moderate 64 | .102689 | .102689 | .0271555 | .0244355 |
| High 12 | .000731298 | .000642862 | .0145527 | .000632874 |
| High 32 | .0000391881 | .0000391881 | 7.46949e-8 | 6.09716e-8 |
| High 64 | .00000219199 | .00000219199 | 1.35414e-19 | 1.11887e-19 |

At moderate64, combined mean width after 512 expansions 2.44355 pp vs original 10.2689 pp, 76.20% reduction. Bound remains several percentage points, not a uniformly accurate local-value oracle. At high64, affinity alone yields a tiny bound without enumerating any outcomes; this is an engineered high-information regime, not general exponential search compression. Width 1.11887e-19 is probability, not percentage points; numerical decimal display of exact BigInt rational difference. High32/64 all combined intervals narrower than TV at every tested ceiling. Weak32 at 128, moderate12 and high12 at 512 each have one root where combined is slightly wider due to different best-first expansion orders. Local envelope tightening does not imply fixed-budget search dominance; could run both engines or intersect outputs at additional cost. Max heap 513 for unique deep fixtures at 512 binary expansions; not physical bytes. C elapsed 3.246s in JS isolate; not controlled speed or memory.

## General result and next experiments
Across A/B/C: 260 distinct synthetic roots, 106 raw rational equality checks, 164 roots with exhaustive reference (A 124 grouped, B16, C24), 196 bounded roots, no failed enclosure/monotonicity/reference assertions. Exact arithmetic includes comparisons and interval endpoints; decimal summaries only display. No standalone Node execution, physical memory profiling, Lean kernel check or original Cogentic PDF/formalization audit completed. Import guards added after A/B execution to make the frozen methods reusable, no algorithm changes to prior campaign. Reproduce from repo root:
    node research/certified_recursive_descent/grouped_likelihoods.mjs
    node research/certified_recursive_descent/likelihood_tv_stress.mjs
    node research/certified_recursive_descent/likelihood_overlap_stress.mjs

CRD-14 proposed (not registered): use the local interval as an input to a globally valid static allocation lower bound. Independent branches with fixed per-branch budgets b_i and no sharing of unused actions have success 1-product_i(1-V_i(b_i)); maximize by min-product knapsack recursion over total call budget. This is a lower bound on adaptive optimum when the plan is legal (sequential execution, capacity at least one). For intervals [L_i,U_i] the same recursion bounds best static allocation, while optimistic U_i cannot be used as upper bound for fully adaptive allocation. Investigate a sensor-aware receding allocation policy that charges its planning work and respects active/abandoned states. Compare exact local formula, bounded interval with selective refinement, cheap static allocation, CRD-11 frozen head and exact finite global Bellman oracle on fresh roots. Separately test actual physical CPU/RSS on local environment, and add a correlated-tree extension with CRD-09 conditional messages rather than assuming independence. No new integer-factorization or ECDLP theorem inferred.