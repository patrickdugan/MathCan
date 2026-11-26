# CRD-08 | Terminal-label operator identification and adaptive branching
2026-11-27. Protocol 27369f9c7c8ce85fc84bc42f9166d36602b5f373. Implementation b9beeda0a8fb979a0d3e179a96116f52f6891da5. Frozen receipt 93503ad8898eff219ea709372730dd27df1d4bce. Positive structured operator identification; positive primary tight-budget comparison against depth/random and generic RNN; no demonstrated superiority over learned hard composition, stochastic operators or exact marginal filtering. All results synthetic; no full BPD/TRM or factoring theorem.

## Identification and gauge
Let P be the observed-output distribution rows for the six designed anchor words. Let P_a be those rows after a further action. Under an observable-output Markov state and invertible P, the population relation P_a=P A_a implies A_a=P^{-1}P_a. In prefix coordinates the action is C_a=P_a P^{-1}=P A_a P^{-1}. Products and trace powers are invariant under this similarity. For an independently chosen arbitrary invertible basis transform S, the state row transforms as p -> p S, operator A -> S^{-1} A S, readout as W -> S^{-1} W. Gauge-invariant claims require an identified readout or a joint conjugacy statement; numerical Frobenius residuals are reported only in the fixed observed-output coordinates.

11,520 labeled examples: 6 anchor words x (prefix alone or one of 2 tokens at 2 levels) x 384 observations per cell. Anchor prefixes have c=.10; appended tokens have c=0 or .15. Hidden output labels are permuted. The design supplies anchor words, six labels, and a two-generator alphabet, but no hidden group state or relator to the estimator. This is a favorable full-rank experimental design, not unsupervised discovery. The structured estimator uses a strong permutation/reset prior and fits each generator independently by exhaustive assignment; group relators are checked afterward. Both learned permutations equal the oracle actions in the fixed output labeling. Empirical P minimum elimination pivot .763078, inverse residual checked at 1e-9, max gauge trace-power discrepancy 2.665e-15. The independent permutation-composition implementation agrees on all 36 group products. Fitted reset rates at c=0 and .15: rotation (0,.168076), reflection (0,.143513), versus true (0,.15) each. No held-out atomic token: long words and macro compositions reuse both learned generators.

| Defect (Frobenius norm) | Raw moments | Simplex projected | Permutation fitted |
|---|---:|---:|---:|
| R^3-I | .229654 | .092024 | 0 |
| S^2-I | .168194 | .012787 | 0 |
| SRS-R^2 | .185875 | .091050 | 0 |

Named word orbit [2,5,1,4,0,3] visits all six labels. Trace character [6,0,0,0,0,0]. Construct central projectors from the six word matrices using trivial and sign characters; the complement is standard isotypic. Exact learned permutation projector ranks 1,1,4, with max idempotence defect 1.923e-16 and cross-projector defect 8.327e-17. Raw and simplex-projected matrices have approximate projector traces near 1,1,4 but failed exact idempotence and have high numerical ranks; do not interpret the raw matrices as exact subspace recovery. The standard isotypic block is two copies of a two-dimensional irrep; identifying the individual multiplicity copies requires a further choice of basis, not a canonical decomposition. Noiseless generators are audited; noisy transition matrices include contraction.

## Frozen word test
Generic 8-state, 150-parameter tanh RNN trained on the same labeled rows with 16 epochs, 64 x32 minibatches each, lr .08. Validation 1024 words of lengths 5–7; selects epoch 1 by CE. Gradient max error 1.904e-11. Training set max length four; test 2048 words per regime of lengths 8–14 with novel compositions. Original noise levels {0,.15}; shift {.25,.35}. Test seeds paired across regimes but hidden reset outcomes can differ.

| Model | Original correct /2048 | Shift correct /2048 | Original CE | Shift CE |
|---|---:|---:|---:|---:|
| Exact | 1096 | 373 | 1.414595 | 1.790043 |
| Permutation/reset | 1096 | 373 | 1.415616 | 1.790081 |
| Stochastic projected | 1096 | 374 | 1.428507 | 1.793204 |
| Raw moment | 1096 | 373 | invalid | invalid |
| Hard learned product | 1096 | 373 | 12.844107 | 22.598613 |
| Generic RNN | 303 | 354 | 1.793030 | 1.793458 |
| Uniform | 350 | 334 | 1.791759 | 1.791759 |

Raw moments yield negative coordinates in 181/2048 original true histories (minimum -.161283), hence no CE or Brier score reported. Structured posterior sum-of-class squared error .000323286 original and .000022635 shifted; stochastic .002917976 and .000706783. The small shifted absolute error partly reflects collapse toward uniform, not improved identification. Hard composition shares the MAP decisions but is uncalibrated. Order scramble changes oracle MAP on 1362/2048 test words; structured original correct falls to 500/2048, shifted to 325. Macro products match repeated steps within 1e-8; this is associativity of fitted matrices and new-word transfer, not learning an unobserved primitive. No model training FLOP equivalence: balanced moments and stochastic gradient training are different algorithms.

## Actual adaptive branching
192 fresh binary trees per regime, depths 5–7, uniform independent target label, hidden child transitions depend on parent state. Each expansion reveals only its checked outgoing edge tokens and levels. Every edge costs one call; every terminal probe costs one call, with failure removed. Pruning and selection use observed states, cap and budget; no complete prefix pre-streaming. Exact marginal residual predicts target probability using the path posterior and mean future operator; it deliberately ignores information from failed terminal probes and is not an optimal adaptive Bayes policy. Learned stochastic and structured filters use the same marginal forecast form. Hard composition uses noiseless inferred transitions; RNN scores current target readout rather than a future-rollout forecast. This is a comparison of complete scoring policies, not an isolated neural architecture causal test.

| Solved /192 | Original cap4/24 | Shift cap4/24 | Original cap16/48 | Shift cap16/48 |
|---|---:|---:|---:|---:|
| Depth | 89 | 104 | 159 | 173 |
| Depth/random | 98 | 102 | 162 | 170 |
| Exact marginal | 117 | 130 | 165 | 184 |
| Structured | 119 | 125 | 166 | 182 |
| Stochastic | 123 | 127 | 168 | 184 |
| Hard composition | 118 | 117 | 166 | 179 |
| Generic RNN | 97 | 110 | 161 | 175 |

Original cap4/24 structured vs depth 53 wins/23 losses p=.00076458; vs randomized depth 53/32 p=.0294564; vs RNN 47/25 p=.0127746. vs hard 14/13 p=1; vs exact 5/3 p=.72656; vs stochastic 7/11 p=.48068. Descriptive paired tests, unadjusted for multiple comparisons. Structured mean calls 18.796875 vs depth/random 20.354167. Shift primary-like configuration vs depth/random 56/33 p=.0191866; no established superiority over the other informed policies. The exact marginal can lose to learned models on finite roots because it is a heuristic in a correlated adaptive tree, not the optimal policy, and sampling varies.

On 2248 original depth-baseline decision states, structured changes 556 top choices; stochastic 594, exact 492. None changes the retained *set* on those baseline states. Hence no learned-eviction advantage established. The cap16 configurations reached only 8 pending nodes, so cap16 is effectively nonbinding. Implementation detail: the protocol called deterministic ties latest-arrival; implementation uses descending binary-tree node ID. This is a deterministic depth-first tie rule shared by the arms, but not necessarily arrival recency for previously retained nodes. Record the deviation rather than interpreting as an exact latest-arrival replication.

5,376 test episodes, 118,505 charged prefix/probe calls, zero false accepts. Independent rational certificate and reached-edge replay, and terminal hidden path independently reconstructed by explicit permutations. Bank/peak checks rely on instrumented sizes; replay does not independently reconstruct scheduling/evictions. Peak logical numeric payload (including conservative active+transient bound) at cap4: six-coordinate filters 36 slots (288 float64 bytes), generic RNN 48 (384 bytes), hard 6 (48 bytes). Excludes fixture, scores, IDs, weights, matrices and object overhead. JS isolate elapsed 49.884s including all generation/training/audit, not per-policy CPU or measured RSS. Standalone Node not invoked.

## Correlated branch obstruction and CRD-09
The CRD-06 independent-branch utility formula does not apply to a shared-prefix tree. Exact four-world counterexample: A~Bernoulli(.6), B~Bernoulli(.5) independent; candidate success variables X1=X2=A, X3=B. Marginal top-2 chooses {1,2}, actual success .6; diverse {1,3} success .8. Independent-product approximation incorrectly gives .84 for {1,2}. Enumeration in receipt checks these numbers.

For observed rooted tree with finite hidden states, transition matrices T_vw and terminal evidence likelihood factors l_v, define upward messages
  m_v(x)=l_v(x) product_(w child of v) sum_y T_vw(x,y) m_w(y).
With root prior pi, evidence probability Z=sum_x pi(x)m_root(x). For a candidate probe v and target g, add a failure factor 1{x_v!=g}. If evidence E has positive probability, P(success_v|E)=1-Z(E plus failure_v)/Z(E). Likewise the conditional success of a fixed set of probes is 1-Z(E plus all failures)/Z(E). These are exact tree identities by conditioning and summing child subtrees; they replace independent marginal products. Complexity O(|edges|d^2) for a full upward pass with d hidden states and dense transitions, local message updates can reuse cached subtree products. This is a mathematical proposal, not an executed CRD-09 algorithm.

Next experiment: freeze fresh correlated trees; compare no-feedback marginal policy, exact tree posterior after each failure, diversity/ancestry penalty, and learned operator message passing at matched verifier budget. Separate terminal probe-only selection (where exact conditional utility is tractable) from adaptive expansions (which require considering information gain and future actions). Add small exhaustive optimal-policy oracle for shallow finite trees and a reset-independent control; measure conditional calibration and policy regret, cache memory bytes and message updates. Keep known operators vs learned operators crossed with exact vs approximate inference, to distinguish channel error from dependence error. No factorization complexity result. Main Cogentic paper and companion formalization still unaudited; CRD-01 Lean ledger uncompiled.
