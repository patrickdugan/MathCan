# CRD-05 result | Observable signal passes, recurrent advantage unestablished
2026-11-26. Protocol commit a101fe650f9c54d8efeed8c1fb534a7469981919; implementation d66fec8eb82f8b4332c94e54750d105908e7ba3a; outcome receipt 94f9114974f7ecab55dc3e025df5efc2af437fda. Fresh registered seeds. Status: positive synthetic observability control, FAIL for primary recurrent advantage over the tag heuristic. Secondary results descriptive; no multiplicity correction. No full TRM/BPD or factorization result.

## Teacher and verification
Typed and original generators each use 256 development roots, four behavior trajectories per root. Typed: 1,336 contexts, 6,428 forced-action rollouts, 65,785 incremental teacher calls, 2,420 unordered same-depth pairs (4,840 oriented examples). Original: 1,115 contexts, 4,916 rollouts, 49,102 incremental calls, 1,571 pairs (3,142 oriented examples). Each candidate gets two common-random-number fallback draws. All teacher traces replayed with their shared prefix; incremental calls exclude prefix. Two draws give a coarse Monte Carlo target, not a precise conditional probability estimate. The typed/scrambled learners receive identical teacher outcomes and training contexts, with only the per-layer permuted observation changed.

| Development diagnostic | Typed | Original |
|---|---:|---:|
| Unequal utility pairs | 602/2420 (24.88%) | 436/1571 (27.75%) |
| Teacher draws disagree (per candidate) | 384/3214 | 248/2458 |
| Tag comparator correct on different-tag unequal-utility pairs | 219/292 (75%) | 113/216 (52.31%) |
| Scrambled tag comparator correct | 138/306 (45.10%) | 96/207 (46.38%) |
| Equal-tag pairs with unequal utility | 310/1265 | 220/759 |

The exact full-feature-signature equality diagnostic yielded zero pairs in both regimes. Continuous/age features make this grouping too fine to estimate the conditional irreducible error. Do not interpret this as proof of unique predictive information or of action exchangeability. The tag comparator rates above are on selected development pairs and are not population estimates. Near-budget sampling and same-depth restriction changed the distribution from CRD-04, so the changed tie rates are not a paired causal comparison.

8 epochs, 48 batches of 32 examples per epoch, lr .08, 8-parameter linear and 137-parameter tied three-step recurrent scorer; weighted symmetric pairwise logistic loss. Maximum finite-difference gradient error 4.83e-12. Typed linear/recurrent and scrambled linear/recurrent select epoch 1; original linear epoch 4, recurrent epoch 1. Validation roots separate from development and test; no test tuning. Full receipts contain weights, checkpoints and counts.

## Registered test outcome
192 fresh test roots per regime. Typed and scrambled observations use the exact same graph, goal and certificates, retaining each layer's tag histogram. Each policy sees the designated tag view only through its scoring function. Both views are stored in the synthetic fixture and the observation intervention is enforced by code, not an external information boundary.

| Typed roots solved /192 | cap4/64 | cap16/64 | cap4/128 |
|---|---:|---:|---:|
| Depth/latest | 114 | 130 | 137 |
| Depth/random ties | 127 | 140 | 146 |
| Tag-only | 135 | 159 | 142 |
| Linear learned | 135 | 159 | 142 |
| Recurrent joint | 128 | 162 | 131 |
| Recurrent ranking only | 126 | 162 | 129 |
| Tag-only scrambled | 121 | 135 | 143 |
| Recurrent scrambled at inference | 108 | 129 | 133 |
| Recurrent trained/evaluated scrambled | 108 | 129 | 133 |

Primary cap4/64: recurrent vs depth/random 30 wins, 29 losses, p=1; vs tag-only 26 wins, 33 losses, p=.435. Mean realized calls 44.18 recurrent, 44.28 tag-only, 50.24 depth/random. No recurrent advantage. The two learned linear/typed and tag-only policies match aggregate results and scheduling decisions on the sampled baseline states. The learned linear policy should not be credited with an independent gain.

Secondary cap16/64: recurrent vs depth/random 37 wins, 15 losses, p=.003185; vs tag-only 21 wins, 18 losses, p=.74926. Recurrent vs its own scrambled-observation intervention 42 wins, 9 losses, p=.000003389; tag-only vs scrambled-tag rule 31 wins, 7 losses, p=.00011617. These are descriptive exact paired sign tests; the protocol's primary model-vs-heuristic comparison failed. At cap4/128 the true recurrent scorer even loses two aggregate solves to its scrambled counterpart; no claim of uniformly beneficial information. At cap16/64 the ranking-only and joint policies tie on every root. This pilot supplies no demonstrated benefit from learned eviction beyond learned ranking at the larger capacity.

Original control cap4/64: depth/latest 148, random ties 147, tag-only/linear 152, recurrent 142, ranking-only 144. Recurrent vs depth/latest 20 wins, 26 losses, p=.4614. No recurrent gain and no strong relation-tag signal on development. The typed generator is deliberately engineered to make tags predictive; it is not evidence that such tags exist in integer factorization, Lean search or any other real environment.

## Action changes and scope
On 2,509 primary typed baseline decision states, recurrent joint changes 1,668 top choices and 370 retained sets; ranking-only changes 1,668 top choices and zero retained sets. Tag-only and linear each change 595 top choices and 139 sets. This repairs CRD-04's policy-equivalence failure but does not demonstrate improved learning over the observable tag heuristic. The ranking-only control recomputes both the classical trim and learned ordering, charging both score-evaluation counts. Capacity counts persistent pending destinations, excluding shared path storage, observed maps and fixture; it is not physical RAM.

Total 11,344 teacher rollouts, 114,887 incremental teacher calls, 8,640 test episodes, 412,463 charged test verifier calls; independent exact arithmetic/path replay passed and zero false accepts. End-to-end JS isolate runtime 26.917 s; not an isolated CPU/RSS benchmark. Source bodies were executed; standalone Node CLI and Lean compilation still need verification. The Cogentic PDF and companion Lean proof have not been directly audited in these steps.

## CRD-06 proposal: compositional observability (not registered or executed)
The next regime should separate a one-step relation feature from information that becomes useful only when combined across observed transitions. Use a finite latent-state process with noisy typed observations and known symmetries. Construct matched fixtures where each individual observation has the same marginal law for productive and unproductive continuations, yet a sequence of two or more observed transition symbols carries predictive information (e.g. a parity or finite-group state). Include a history-scrambled view preserving individual symbol histograms, graph and verifier outcomes; show that the intended conditional information gap holds before fitting. Exact Bayesian filtering or finite-state update is the algorithmic reference, together with latest-tag, history count, fixed-window linear/MLP, and depth/random baselines.

Train a stateful shared-weight recurrent filter on observable histories, rather than reinitializing the hidden state for each seven-dimensional candidate. Keep one hidden state per retained branch and account for its memory. Compare an explicit posterior filter against learned recurrent state, and test variable-length, unseen-depth generalization. A parameter-matched nonrecurrent history model is mandatory. The capacity and budget protocol must charge updates, verification, duplicate paths, candidate storage and memory. Only after an advantage over strong classical and memory-matched neural controls should this proceed to the full BPD steering/MMS integration. Prefer a fresh prospective protocol over post-hoc optimization of CRD-05 test seeds.
