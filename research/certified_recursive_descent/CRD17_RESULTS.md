# CRD-17 | Deadline-aware screening and admissible information relaxation
2026-11-27. Registered at e2cd94731a7a8d6cac0235c049e6d16f2281521b; source commit 784bf5067b2bacf39b106e22487b0b4b02f64955, blob e130cedd81d55384ef9cec5860f09c5fe841a4a5. Frozen CRD-16 import guard/export commit b99bdf12b56ecba9a1e68c4a9d19ae07c8c38563. Receipts standard 9d0a44d756bccaaf96a919b76933c38a987d91da (blob 9799c3fd53da58bc532639a676576f550a5d0e63), deeper 30fe040fa0b28a15e8e733f5f09116f16aa0633c (blob 08090876bc3f766a2fa473eb06618e75110abedf), tight 61b5d846edb8d30a5defae7620fa1ce99ea05293 (blob c32e50ab1e97ad19cfe0db7ca2f69741da480790). All three read back and parsed. Continues draft PR #291. No new training or parameter tuning.

## 1. Deadline relaxation theorem

Assume the CRD-11 finite independent-branch model, with mandatory sequential sensors, disjoint feasible terminal states, unit action cost, and budget b. Relax active capacity and irreversible abandonment. For any branch with m_i>0 remaining sensors, reveal its true hidden state when paying the first remaining sensor, while preserving the remaining m_i-1 sensor costs and one terminal probe. An already-ready branch (m_i=0) keeps its original terminal uncertainty. The original policy is feasible in this enlarged information/action model by ignoring additional information. Hence the relaxed optimum upper-bounds V*. A branch with m_i+1>b cannot succeed, so omit it.

If a paid screen reveals a feasible hidden state and m_i further actions fit, the relaxed controller can finish and succeed with probability one. If it reveals infeasibility, further actions on that branch cannot succeed; its observations convey no information about other independent branches. Randomized decisions cannot improve finite optimal expected utility. Along a deterministic policy's all-failure continuation, the controller therefore attempts selected one-cost screens, together with ready probes. Screen i must occupy a position no later than d_i=b-m_i (one-based). On its success the other actions are unnecessary. Reordering screens before ready probes and sorting screens by ascending deadline preserves feasibility whenever the original ordering was feasible: swap adjacent inverted deadlines, with both originally feasible, and move unconstrained ready probes after screens. Reordering leaves the eventual selected event union unchanged. All-failure outcomes for different independent branches factorize; ready probes within a branch are disjoint, so the highest t posterior masses attain the best t-probe success. This gives a tractable exact relaxed objective.

Process unready branches by nondecreasing d_i. Start a failure-product DP with D(0)=1, other entries infinity. For screen i either skip, or update D_next(t+1)=min(D_next(t+1),D(t)(1-f_i)) when t+1<=d_i, where f_i is its posterior feasible mass. Convolve the ready branch options k=0..3 at cost k with failure factor 1-topSum_k(p_i). Take U_deadline=1-min_{t<=b}D(t). Complexity O(n log n+n b) arithmetic/combinations for three feasible states per branch, plus descriptor extraction and overhead. This is not a general solution to adaptive optional sensing, correlated branches, variable costs or overlapping terminal events.

The CRD-15 prophet bound U_prophet=1-product_{individually affordable i}(1-f_i) ignores competition. For each selected screen/probe plan its branch success probability is at most f_i, so U_deadline<=U_prophet. The true model's static allocation is a lower bound F<=V*<=U_deadline. When there are zero/one affordable branches or all affordable branches are ready, CRD-15's exact shortcuts still apply. At other nodes, min of existing U and U_deadline is an admissible envelope. A second variant intersects with T U_deadline, a one-step actual Bellman backup over actual legal actions and conditional observations (including eviction). This is admissible by monotonicity because U_deadline>=V*. Backed bounds add computation even though they do not spend planner expansion quota. These mathematical inequalities are exact under the assumptions; the deployed numerical implementation uses double precision, clipping and tolerances, not verified outward rounding.

## 2. Independent checks and experiment design

Fresh roots: 64 standard seeds 2320001..2320064, three branches up to 3 sensors, cap2 budget6; 32 deeper seeds 2330001..2330032, up to 4 sensors, cap2 budget8; 48 tight seeds 2340001..2340048, each branch 3 or 4 sensors, cap1 budget5. Last cohort deliberately engineered for competing deadlines. No previous test roots or fitting. Each cohort uses the same roots across policy arms.

Three persistent sparse indexed DAG planners: prophet, deadline, backed. Identical per-trajectory new expansion ceiling 16/48 and per-decision quota min(16,R-(b-1)); retain/copy observed reachable descendants with reverse links rebuilt. Each counterfactual continuation receives its own copy and remaining work budget; no sibling warm start. All reset deterministic allocation and upper caches per decision. Pre-intern every possible positive-feasible local posterior using the public model, in deterministic order, for each policy and oracle to neutralize intern-ID tie changes. This differs from CRD-16's lazy interning; all three current arms share setup. Setup counts per cohort per arm: 4247 states/13052 local outcomes standard, 2538/7615 deeper, 5557/16115 tight. No observed hidden outcomes are used. This precomputation is extra public model work and storage. Sparse F and DAG logic otherwise frozen. Deadline cache keyed by canonical complete continuation descriptors and b; retained Bellman DAG remains indexed. Extra warm outcomes do not become retained expanded edges. Work recorded separately, including copied graph entries, allocation combinations, bound combinations, warm transitions, backups and setup.

Four hand examples checked in each cohort. Deadline DP matches independent relaxed Bellman recursion and BigInt exhaustive subset/count enumeration on 1,024 root/budget combinations and 722 sampled labeled-oracle decision states (1,746 reference comparisons). The relaxed reference explores 5,464 states and 7,789 actions; integer enumerator checks 6,284 feasible plans. Maximum discrepancy 2.22e-16. On every reference state verify actual oracle V<=deadline<=prophet. Every reached policy action checked against aligned exact Q intervals and numerical regret gaps; separately compare original deadline and backed envelopes at the reached state using oracle-side model calculations, excluded from planning counters. All expected cumulative regret checks pass.

## 3. Results

Expected success by finite-model conditional evaluation, not observed binary trial rates.

| Cohort | Exact | Receding2 | Prophet16 | Deadline16 | Backed16 | Prophet48 | Deadline48 | Backed48 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Standard | .75365846 | .75198523 | .73949527 | .74868848 | .75229299 | .74913751 | .75305274 | .75341211 |
| Deeper | .81274757 | .80967125 | .80281586 | .80352221 | .80428067 | .80833256 | .80976608 | .81104410 |
| Tight | .55272988 | .55272988 | .55272988 | .55272988 | .55272988 | .55272988 | .55272988 | .55272988 |

Primary standard Deadline48 vs Prophet48 +.00391522 (0.39152 pp), descriptive paired bootstrap 95% interval [.00138323,.00676967], wins/losses/ties 11/2/51. Versus receding2 +.00106750 [.00003218,.00236903], 7/4/53, with different work budget. Backed48 vs Prophet48 +.00427459 [.00176607,.00724577], 15/0/49; vs Deadline48 +.00035937 [.00000108,.00079756], 6/1/57; regret .00024635 (0.02464 pp), 61 roots tie optimum, 3 below. Deadline16 vs Prophet16 +.00919322 [.00519076,.01368201], 21/0/43. Backed16 vs receding2 +.00030776 interval crosses zero. Deeper Deadline48 vs Prophet48 +.00143352 [.00008200,.00338393], 8/1/23; Backed48 +.00271154 [.00063063,.00521863], 13/1/18. Deeper Backed48 vs receding2 interval crosses zero. All tight policies tie exact optimum. Bootstrap 2,000 fixed root resamples, descriptive, unadjusted. Do not claim universal policy dominance from tighter bounds: some paired losses occur.

At full-budget roots, deadline upper equals prophet for every standard and deeper fixture: all screens can fit in the all-failure schedule. Tight cohort improves 48/48 root upper bounds: mean prophet slack .315373 vs deadline .218580. At states reached by standard Deadline48, strict improvement rate 40.57%, mean prophet/deadline/backed slack .0946724/.0477840/.0296531 (unweighted over offline visits to the same states, raw envelopes, before exact shortcuts). This explains why improvements emerge below the root even when the initial bound is unchanged.

## 4. Computational accounting

Expected per realized trajectory at total48, standard:
| Work | Prophet | Deadline | Backed |
|---|---:|---:|---:|
| New planner expansions | 37.138 | 34.402 | 28.239 |
| New planning outcomes | 279.194 | 247.505 | 208.195 |
| Allocation combinations | 2184.23 | 2405.37 | 2298.63 |
| Deadline bound combinations | 0 | 782.20 | 2234.64 |
| Additional warm outcomes | 0 | 0 | 738.14 |
| Backups | 122.347 | 106.473 | 82.337 |
| Copied DAG nodes | 66.157 | 51.627 | 45.053 |
| Copied outcome edges | 89.954 | 62.732 | 53.465 |
| Peak per-decision retained entries | 159 | 132 | 118 |
| Expected certification rate | 61.37% | 66.95% | 74.08% |
| Expected cumulative gap | .206433 | .151595 | .087324 |

Backed48 reduces planner expansions by 23.96%, but additional bound work is substantial; matched node ceiling is not matched overall compute. Deadline48 uses 7.37% fewer new expansions and more allocation combinations than prophet. Standard expected calls 5.0522/5.0730/5.1022 for prophet/deadline/backed48, respectively. The backed policy also changes evictions; no causal eviction benefit isolated. Deeper new expansions 41.646/41.577/40.542, bound combinations 0/1138.18/4072.97, extra warm outcomes 0/0/968.58; certification rates 45.56%/46.66%/52.39%. Tight new expansions 8.171/7.059/6.019 for either ceiling, all decisions certified, same 114.04 allocation combinations, deadline/backed add 18.31/34.60 bound combinations, backed adds 28.75 warm outcomes. This is favorable for planning-node economy, not established runtime dominance. Counts of different units must not be added as if equal-cost FLOPs. Pre-intern overhead and copying matter. No physical memory cap or measured latency comparison.

## 5. Verification

144 fresh roots, 864 bounded-planner root-policy expectations plus 144 exact and 144 receding2 expectations = 1,152 total (excluding extra audit budget queries). 36,549 reached decision visits across offline counterfactual evaluation paths, 96,026 Q interval comparisons, 31,714 numerically certified visits. Maximum numerical Q/state interval violation 3.33e-16; reached raw bound violation 2.22e-16; maximum gap-bound violation 1.11e-16. All path expansion maxima <=48, all action budgets respected, all expected regret telescoping checks pass. Backed48 standard cumulative gap .087324 vs actual regret .00024635 remains very loose. End-to-end JS isolate runs 8.967/10.390/2.033 seconds including references, setup and audits, not controlled runtime. Three receipts parsed successfully.

Reproduce from repository root:
    node research/certified_recursive_descent/deadline_relaxation.mjs
    node research/certified_recursive_descent/deadline_relaxation.mjs --deep
    node research/certified_recursive_descent/deadline_relaxation.mjs --tight

Standalone Node invocation not performed; concatenated committed source bodies run in JS isolate with dependency checks. No Lean kernel run, physical RSS measurement, full TRM/BPD integration, actual proof-search verifier or original Cogentic factoring proof audit. This experiment concerns independent synthetic decision problems.

## 6. CRD-18 proposal (unregistered)
Use lazy upper tightening rather than compute the expensive backed bound on every new node. Begin with prophet/exact shortcuts. On overlap, charge the next refinement choice in common explicit operation units: cheap deadline DP, one-step warm backup, or actual DAG expansion; retain whichever computation supplies a reusable bound or descendant graph. Count deadline combinations, outcome evaluations, local formula work, backups, sorting/canonicalization, and copy work separately, then test a prospectively fixed weighted work proxy and equal measured wall-clock on local hardware if available. Compare a simple deterministic escalation rule to CRD-17 always-deadline/backed with matched total work, and test the option to cache the warm-backup edges as an actual expanded node to avoid duplicated outcome work. Tighten upper bounds for capacity-one states by accounting for irrevocable eviction of active branches; derive admissibility before testing. Full canonical persistent graph and correlated cases remain separate work. No new factoring theorem follows.
