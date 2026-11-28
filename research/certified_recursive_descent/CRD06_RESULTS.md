# CRD-06 result | Persistent multiplicative filter generalizes, ordinary RNN fails
2026-11-26. Protocol commit 3ee0381d5604571af8c07721ef70a6dc8c1f41a7, implementation c1e61d238de3815a696137c04b71599798932147, receipt 6e684292dca763b6651844e64dbc83c29ad30fa8. Registered fresh independent-chain fixture. Status: generic recurrence gate FAIL; architecture-informed scalar filter PASS against generic neural and random controls, approximate exact-Bayes calibration. This is not an independent discovery of parity, a full TRM/BPD, or a factorization result.

## Exact information identities
Let X_i be independent uniform signs, R_i independent reliability in {.90,.98}, Y_i=X_i E_i, with E_i independent given R_i and E[E_i|R_i]=R_i. Z_L=product X_i. Conditional on all observed pairs, the X_i remain conditionally independent, and E[X_i|Y_i,R_i]=R_i Y_i by Bayes symmetry. Consequently

    E[Z_L | Y,R] = product_i R_i Y_i
    P(Z_L=+1 | Y,R) = (1+product_i R_i Y_i)/2.

For any proper subset of observed transitions (with all reliabilities or only subset reliabilities supplied), at least one unobserved independent uniform X_i remains. Its conditional expectation is zero, so the product has conditional expectation zero. Thus the subset is independent of terminal parity given sequence length and reliabilities. In particular the last-four observation window is information-theoretically insufficient when L>4; the fixed-window control is expected to fail. A full-history MLP can in principle represent the map; the tested 85-parameter model trained only on short sequences is not a universal impossibility result. The number of negative observed signs determines the MAP class exactly, so a parity/count-mod-2 baseline has the same classification as Bayes; the ordinary signed-mean count baseline does not compute parity.

Exact integer enumeration (alternating .90/.98 reliability, lengths 2..8) checked 508 observation vectors, 87,376 latent/observed sign-vector pairs, 70 individual-hidden-sign independence checks. Channel weights use integer likelihood factors out of 100; all posterior identities passed. Enumeration is bounded evidence supplementing the mathematical proof, not a statistical approximation.

## Training and held-out sequence results
8,192 training sequences, lengths 2..8; 1,024 validation, lengths 9..12; 2,048 test, lengths 13..20. Models trained with registered 16 epochs x 64 minibatches x 32 examples, SGD lr .08, no test tuning. Selected by validation BCE: RNN epoch4, window/full MLP epoch1, multiplicative epoch16. Gradient finite-difference maximum error 4.81e-11. Weights and length-specific results in receipt. Full-history MLP left-pads to 40 input slots; early slots unused by short training sequences, an intentional fixed-coordinate extrapolation challenge rather than equal capacity at every depth.

| Model | Parameters | State scalars | Held-out correct /2048 | BCE | Posterior MSE |
|---|---:|---:|---:|---:|---:|
| Exact Bayes | 0 learned | 1 | 1387 | .621753 | 0 |
| Hard parity | 0 | 1 | 1387 | 8.91802 | .102653 |
| Last symbol | 0 | 1 | 1006 | 14.05837 | .285499 |
| Signed mean | 0 | 2 | 1024 | .725726 | .050744 |
| Random | 0 | 0 | 1038 | .999995 | .116383 |
| Generic tanh RNN | 33 | 4 | 991 | .693846 | .035017 |
| Fixed-window MLP | 31 | 8 | 993 | .693950 | .035386 |
| Full-history MLP | 85 | 40 | 1012 | .694075 | .035220 |
| Multiplicative | 4 | 1 | 1387 | .621679 | .000093965 |

Hard parity/last return endpoint probability 0 or 1; BCE is clipped at 1e-12, so their large BCE measures overconfidence, not poor discrimination alone. Exact Bayes minimizes expected proper scoring loss; the slightly lower empirical BCE for the learned model is sampling variation and does not establish improvement over the true posterior.

Multiplicative filter: h_0=1, h_t=h_(t-1)*tanh(w0+w1*Y_t+w2*C_t+w3*Y_t*C_t), C_t=(R_t-.94)/.04. Aligned initialization [0,.8,0,.1] gives the correct factor sign even before training. This strong inductive bias supplies the parity mechanism. Training learns approximate reliability factors, rather than discovering composition from scratch. Selected weights [-.12953623234048023,1.8945735772890162,-.17275177883453136,.42683193914083006]. Learned factors for (Y,R)=(-1,.90),(-1,.98),(+1,.90),(+1,.98): -.890539,-.989533,.907109,.965354. Max factor absolute deviation .014647; all signs correct. Therefore mathematically its MAP class matches exact Bayes for every finite history (excluding floating-point underflow), explaining identical classification per length. Calibration improves on the supplied hard parity rule.

## Search and memory
192 fresh search roots, 16 independent branches each, unique 3,072 branch seeds. All roots happened to have at least one positive branch. All 16 prefix histories are read and each arithmetic edge checked before observing its symbol. All arithmetic edges deliberately valid; the terminal verifier checks the latent sign product. This is a controlled streaming top-k selection task, not a branching DAG or real proof-search implementation. At most one active branch plus retained complete states, online score trim at each arrival; prefix costs identical per policy and probe count. A policy cannot avoid prefix work. Independent arithmetic check on each executed prefix (BigInt cube/slack) and exact terminal witness check; zero false accepts. Per-step observation permutation across branches preserves the multiset, not their association with hidden signs; finite permutation can leave some symbols unchanged.

| True observations, solved /192 | 1 probe cap4 | 4 probes cap4 |
|---|---:|---:|
| Exact Bayes | 142 | 190 |
| Hard parity | 136 | 191 |
| Last symbol | 104 | 180 |
| Signed mean | 104 | 187 |
| Random | 98 | 178 |
| Generic RNN | 96 | 186 |
| Window MLP | 104 | 182 |
| Full MLP | 92 | 184 |
| Learned multiplicative | 140 | 190 |

Primary cap4/one probe: scalar vs window 61 wins/25 losses, exact paired p=.0001304; vs random 65/23, p=.00000850; vs Bayes 8/10, p=.8145; vs hard parity 39/35, p=.7275. Scalar true vs scrambled (140 vs 97) 75/32, p=.00003919; Bayes true vs scrambled (142 vs 97) 72/27, p=.00000690. Generic RNN vs window 39/47, p=.4505; vs random 46/48, p=.9179. These are descriptive unadjusted tests. The generic recurrence hypothesis fails; scalar's structured gain is not a significant advantage over the exact algorithm or hard parity. At four probes, cap4 and cap16 have identical ordered probe traces, as expected for static top-k scores and full prefix coverage. More storage above probe count has no demonstrated benefit.

Primary mean calls 271.4167 per root (270.4167 prefix +1 terminal); with four-probe ceiling scalar mean terminal 1.375 vs Bayes 1.3802 and parity 1.4271. One active branch plus cap4 bank: peak numeric-state payload scalar/Bayes/parity 5 slots=40 bytes at float64, generic RNN 20=160, window 40=320, full 200=1600. These are logical payloads excluding scores, IDs, parameter storage, array/object overhead and shared fixture; the implementation simulates both bank sizes together, so they are not measured RSS or the combined process footprint. State updates and score reads logged per configuration. Analytic operation counts in receipt; same verifier budget is not equivalent to equal CPU cost.

10,368 logical policy/root/config episodes, 2,803,680 logical prefix checks plus 15,660 actual terminal probes. Shared identical prefix execution for all three cap/probe configurations of each policy/view: 934,560 physically executed prefix checks, each checked independently; the factor of three in logical accounting is reuse, not extra actual executions. All configured terminal probes executed, including repetitions across logically separate configurations. JS-isolate end-to-end runtime 6.759s, including generation, training and verification; standalone Node and actual RSS remain untested.

## Useful conditional decision theorem
For independent branch success variables with conditional posterior probabilities p_i, the probability of success after probing a fixed subset S of k candidates is 1-product_(i in S)(1-p_i). Swapping a lower-p retained candidate for a higher-p unretained candidate weakly improves this quantity. Thus the top-k posterior subset is optimal given the observation and independence law. Stop-at-success does not affect the success probability. For a sequential choice with fixed posteriors, probing those k in decreasing p also minimizes expected probes by adjacent exchange. This does not extend directly to dependent proof branches or informative failure observations.

If approximate scores q_i satisfy sup_i |q_i-p_i|<=epsilon, and S_p,S_q are respective top-k sets, then V_p(S_p)-V_p(S_q)<=2k epsilon. Proof: product telescoping gives |V_p(S)-V_q(S)|<=k epsilon for every S; use q-optimality and two triangle terms. For scalar multiplicative filters with factors f_i,g_i of magnitude <=1 and maximum per-factor discrepancy delta, |product f_i-product g_i|<=L delta; hence posterior error <= L delta/2. With a uniform magnitude bound rho<1 the sharper estimate is L delta rho^(L-1)/2. These are conditional deterministic bounds, not estimates of typical test error.

## CRD-07 proposal (not registered or executed)
Move from the scalar character of Z2 to noncommutative finite-group state S3. Hidden increments independent uniform group elements, observed symbols from a known noisy channel, terminal target a group element or coset. Any proper subset of increments still leaves the product uniform. Noncommuting observed updates make within-history order relevant, providing a stronger scramble control. Exact reference is a six-coordinate posterior updated by group convolution; in Fourier coordinates the update decomposes into the trivial, sign and two-dimensional irreducible blocks. Compare direct Bayesian convolution, hard group product, learned blockwise multiplicative recurrence, generic RNN and parameter/memory-matched full-history models. Audit exact posterior, order scrambling, update cost, calibration and top-k regret. This connects to BPD as structured operator/block decomposition rather than merely retaining extra candidates. Learn channel/operator parameters from short histories and test on new depths and a registered noise shift. Full TRM/BPD integration still requires a realistic proof/search environment, not solely this engineered latent task.

The main Cogentic PDF and companion Lean formalization remain unaudited; CRD-01 isolated Lean ledger uncompiled. No new factorization or ECDLP complexity result follows.
