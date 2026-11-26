# CRD-10 | Memory-budgeted inference and information acquisition
2026-11-27. CRD-10A protocol d306e06622538d4834050b6690ba0b2dd0f633a7, implementation 2c65330576433fe23f574237422177c66e0cfe20, receipt d54bdc5b834f6fc1e81a5da510a0cd01578f3e88. CRD-10B follow-on protocol ab5a26be2c8e1c198e74ff0c86b6c30b85a4ef1f, source a74050066b23bd39c984e8e4bcde7db2a623bc57, receipt b69ac0392453621f4c5843cfb73ad8fa89c558e5. Positive exact-engine work reduction, null primary tight-ceiling solve gain in 10B, positive small finite adaptive-oracle value gap. No new training, full BPD/TRM, physical memory claim or factoring theorem.

## Exact inference and score reuse
Store observed tree records, candidate bank scores, and a bounded LRU cache of upward edge contributions. Parent/children follow ternary heap indexing. Factorized transport under reset-permutation channel T=(1-c)P+cJ:
    Tm=(1-c)Pm+c mean(m) 1,
    pT=(1-c)pP+c sum(p)/d 1^T.
No dense transition tables stored. Shared future target vectors computed from public channel and token law, not observed future edges. Failure flags and subtree failure counts invalidate only ancestor messages. A subtree with no outcome evidence has unit message; skip transport. Path engine queries separately; batch shares downward prefixes on union of queried paths. Both use the same upward cache. Lazy engine reuses previously computed scores and evaluates only candidates needed to certify next choice and retained set. Does not require ordering every nonselected candidate; ranking recomputed at next step.

Let E subset E0 with positive P(E0), P(E), and f in [0,1] fixed for a candidate. Conditional distribution under E0 is a mixture of distribution under E with weight w=P(E)/P(E0), and distribution under E0 minus E with weight 1-w. Thus |E[f|E]-E[f|E0]| <=1-w; equivalently TV distance is at most 1-w (equality if events viewed on full outcome space). Since a newly revealed transition token/channel is generated independently of hidden state and terminal evidence in this fixture, adding a child observation without a terminal outcome leaves existing posterior utilities unchanged. Future forecast f fixed across versions. Use score intervals clipped to [0,1] and depth-preserving rank. If every retained lower-bound rank exceeds every excluded upper-bound rank and the selected top lower bound dominates all competitors, the exact top choice and set are certified. Otherwise refine ambiguous scores. Each refinement resolves at least one stale entry; exact ties use descending node ID. Bound is model-conditional and exact in real arithmetic; implementation uses floating-point, 1e-12 quantization/padding, not interval arithmetic or a formally verified floating-point certificate. Independent dense audit checks scores and rank decisions.

## CRD-10A frozen arena result
192 roots per regime, ternary depth 4–5, verifier ceiling 48. Correlated and independent-final-reset regimes. B=256 or 512 logical slots, cap2/4/8. B includes five conceptual slots per observed record, reserved four slots for each of cap+2 bank entries, six per stored message vector. LRU shrinks with observed-record growth. This is a persistent payload accounting model; no physical heap limit or scratch bound enforcement. In particular JS Map/Array/object overhead, shared fixtures, audit traces and transient query scratch are outside B; an inserted cache vector may temporarily exist before trim. Reported scratch upper is a conservative estimate of numeric query payload, not a measured or verified complete allocator bound. Shared forecast vectors occupy 792 slots in execution; shared permutations 12 entries. No memory stops in tested settings; B is active on cache evictions at cap8, not on record admission.

| Correlated B512 cap4 | Solved /192 | Transports | Posterior queries | Peak persistent slots |
|---|---:|---:|---:|---:|
| Path | 113 | 18442 | 5619 | 179 |
| Batch | 113 | 11277 | 5619 | 179 |
| Lazy | 113 | 8075 | 3296 | 179 |
| Marginal/no feedback | 113 | 9185 | 5648 | 119 |
| Depth | 103 | 0 | 0 | 119 |

All three exact engines have identical complete trace, next candidate and retained-set decisions in all 4,608 pair comparisons on fresh roots. Dense oracle rank audit: 1,000 scheduling states and 3,644 fresh score checks, maximum absolute error 2.776e-16; 204 top changes and 68 retained-set changes vs depth/node-ID across audited engine-states (counts include repeated comparable states across engines). Lazy primary 56.21% fewer transports than path, 28.39% fewer than batch; 41.34% fewer posterior evaluations than either. Upward transport count same (2175) across exact engines at primary; savings mainly downward reuse (16267 path, 9102 batch, 5900 lazy). Lazy records 2733 previously cached entries encountered (may still require refinement), 1442 certified rounds. Peak 179 slots = 1432 float64-payload bytes under declared model, not RSS. Primary candidate cap4 exact and marginal solve counts tie; inference efficiency is the identified gain.

| Correlated B256 | cap2 | cap4 | cap8 |
|---|---:|---:|---:|
| Exact engines | 79 | 113 | 170 |
| Marginal | not run | 113 | 158 |
| Depth | not run | 103 | 154 |

At cap8, same 256-slot B, path 38995 transports, batch 22507, lazy 13579, all solve 170/192; lazy cuts transport 65.18% vs path. Lazy cache evictions 748 at B256 vs zero at B512; B512 lazy transports 13413, peak slots 357. At B256 all exact engines peak 256 slots; no change in solve count when cache shrinks, because exact recomputation preserves decisions. Cap8 vs cap4 also changes realized mean calls (24.802 vs 18.531) within common 48-call ceiling. Higher retention trades memory and calls for more successes. At cap8 lazy vs marginal 16 paired wins/4 losses, p=.01182; vs depth 33/17, p=.03284. Descriptive unadjusted secondary tests. Independent-final-reset exact engines, marginal and depth at cap8 all solve 179/192; feedback has no information advantage. The registered 256-transport cap at B256/cap4 never binds, so it establishes no work-constrained solve advantage.

## CRD-10B prospective tighter ceiling after 10A
Motivated by the nonbinding 10A ceiling. New disjoint seeds 1660001..1660192; protocol committed before generating roots, unchanged runner logic. B256 cap8, 48 verifier calls, correlated and independent controls. Deterministic transport caps 64 (primary),128 (secondary) or unlimited. If transport limit reached during ranking, count partial work and use depth/node-ID fallback; all subsequent inference attempts are still blocked at the same ceiling. Equal transport limit is not equal CPU time.

| Correlated | 64 solves | 128 solves | Unlimited solves | 64 fallback roots |
|---|---:|---:|---:|---:|
| Path | 156 | 156 | 163 | 163 |
| Batch | 156 | 156 | 163 | 116 |
| Lazy | 156 | 162 | 163 | 82 |

Primary 64 cap: exact solve-count tie, all paired wins/losses zero, so the hypothesis of improved success at that ceiling fails. Lazy consumes 8734 transports vs 11882 path and 10516 batch; 82 roots with any fallback vs path 163/batch116. At 128 cap lazy 162 vs 156 both controls, paired 10/4, p=.179565; no statistically established solve advantage. Unlimited lazy 14805 vs 42178 path and 24652 batch, all exact engines agree on 163 solves. Marginal and depth each 155. Independent control all configurations solve 181/192, with no utility gain. Unlimited trace comparisons 768/768 match. No arena admission stops. Report all nulls; no selection of preferred ceiling after testing.

## Small adaptive information oracle
Separate 192 roots, two independent six-state hidden branches with integer priors and a binary noisy parity sensor. Expanding costs one call, reveals the sensor, unlocks three candidate probes; each probe costs one call and success occurs only when hidden state equals its candidate index. States 3–5 have no successful probe. All continuation probabilities computed by conditioning integer weights and Bellman recursion; floating arithmetic for the probabilities. Exact finite-model optimal policy considers all legal expansions and probes with remaining budget, stopping on success. No-feedback control uses original priors for ranking but legal() excludes zero-posterior and previously failed candidates, so it retains support information; it is not a wholly observation-blind policy. Other controls: depth/probe-first, posterior marginal probe-first, sensor-aware one-step (expected best immediate probe after expansion).

| Expected success | 2 calls | 3 calls | 4 calls | 5 calls |
|---|---:|---:|---:|---:|
| Depth/probe-first | 20.8879% | 38.7238% | 52.1948% | 55.2729% |
| No-feedback rank | 31.3828% | 46.5839% | 54.7654% | 57.7119% |
| Marginal probe-first | 33.8435% | 47.8508% | 55.1360% | 58.1174% |
| Sensor-aware one-step | 35.6469% | 48.3368% | 58.2580% | 66.5282% |
| Optimal adaptive | 35.6469% | 51.2257% | 60.2396% | 66.7116% |

At budget5, adaptive oracle gains 8.5942 percentage points over marginal probe-first; sensor-aware rule within .1834 percentage points. At budget3 sensor-aware remains 2.8889 points below oracle. First optimal action differs from marginal on 100/192 roots at budget5 (ties included); optimal expansion despite available probes selected in 3274 of 31861 DP states explored across budgets, not all necessarily reached under optimal policy. Two hand identities pass, 768 budget-monotonicity checks, independent forward latent-world expectation replay on 48 root/budget combinations (1728 world evaluations), max error 2.22e-16. This is a finite adaptive decision model, not a guarantee that full-tree expansion or real proof search benefits by the same amount.

## Verification, caveats and next steps
10A arena: 11,136 episodes, 221,710 charged edge/probe checks; 10B: 4,224 episodes, 106,653 checks. Total 15,360 episodes and 328,363 charged checks; all reached-edge and terminal witness replays pass, zero false accepts. Unlimited exact trace comparisons 5,376 across both campaigns. Cache budget assertions apply at stable record/cache states, not actual RSS. Independent dense scorer audits a selected subset; trace replay independently checks reachable observations/terminal outcomes, not independent reconstruction of every cache operation. Source bodies executed in JS isolate; elapsed 7.508s/3.576s end-to-end not a controlled benchmark. Standalone Node invocation and physical RAM/CPU profiling still outstanding. Reproduce with node research/certified_recursive_descent/memory_budgeted.mjs and node research/certified_recursive_descent/memory_ceiling_challenge.mjs.

CRD-11 proposed (unregistered): use a learned information-gain head trained on Bellman advantage from small revealed-branch tasks, with posterior-greedy and one-step sensor-aware controls, then test on deeper adaptive trees where probe outcomes and expansions both change posterior information. Preserve certified score intervals and explicitly allocate measured bytes between a compact evidence arena, candidate embeddings and recurrent memory. Include an exact shallow-policy oracle, cap-matched random eviction, no-feedback and cheap heuristic controls; report inference FLOPs and measured CPU/RSS on local Node/Rust implementation rather than extrapolating from matvec counts. No full BPD/TRM result yet. CRD-01 Lean ledger and original Cogentic PDF/formalization remain unaudited/uncompiled as applicable; no factorization or ECDLP result follows.
