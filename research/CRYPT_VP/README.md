# CRYPT-VP-01: spectral geometry in quantum Cryptomania

Status: prospective cryptographic research; QOBS-01 Lean source written, native gate pending. QOBS-02 exact integer pilot executed: 72 cases and 144 direct/spectral comparisons passed. Base: VPVNP-02J certified source b3b3c161ea713b5d1b8866fed1e16eca4ae278f1, closure 8037fc588f76ef49436c6476aaf1a217e55f0833, run 45387078704. No new hardness or security claim.

## QOBS-01: complex observer

For n>=1, uniform independent X in binary n-by-n matrices and A in the actual rank-r matrices, define D_r^2 as the mean squared Hilbert-Schmidt change of f(X). Flatten real and imaginary coordinates of any finite complex matrix. The certified Euclidean theorem yields D_n^2 <= C_n D_1^2, C_n=2(1-2^(-n)), and D_n^2+C_n E_high/3 <= C_n D_1^2. E_high is the rank>=2 denominator-weighted Walsh energy. The statement needs neither positivity nor unit trace. In particular it applies to density matrices and any fixed finite tensor power. Native targets: coordinate identity, energy identity, bound, defect, real phase-entry frequency. All must pass the existing standard-axiom allowlist. The tensor-power corollary is mathematical specialization, not a separate native proof of density-operator machinery.

## QOBS-02: pure phase states

Let p_i>=0 sum to one, alpha_i complex with |alpha_i|^2=p_i, B_i binary matrices, psi_X=sum_i alpha_i (-1)^(<B_i,X>) |i>. The (i,j) density entry is alpha_i conj(alpha_j) times the Walsh character at B_i+B_j. Let mu(B)=sum_{i:B_i=B} p_i. The rank-conditioned squared HS energy of k copies is
D_{r,k}^2 = 4 sum_B (mu^{*2k})(B) Pr_{A:rank r}(<B,A>=1),
where * is XOR convolution. Equivalently, the energy for a shift A is 2(1-|sum_i p_i (-1)^(<B_i,A>)|^(2k)). It is independent of X and complex amplitude phases. For k>=1, D_{r,1}^2<=D_{r,k}^2<=k D_{r,1}^2 by the geometric series identity. Common-row (or common-column) frequency families saturate the sharp comparison whenever nonconstant. More generally equality holds exactly when all positive-weight nonzero pairwise frequency differences have rank one: the rank>=2 gap excludes other support, and rank-one frequencies attain equality. The support for any k contains the original pairwise differences, because repeated pairs cancel, and common-row support is closed under XOR. A complete k-copy equality classification for arbitrary families requires checking the whole convolution support (even if every original pairwise difference is rank one); this is an explicit next proof gate.

For pure states, trace distance T=1/2||rho-sigma||_1 obeys T^2=HS^2/2. With equal priors and known pair of states, optimal success is (1+T)/2. Hence the squared success advantage over guessing is HS^2/8. For mixed states the pure-state identity need not hold; for hidden input, random labels or adaptive coherent queries the pairwise discrimination experiment is a different game. No claim of hiding or unforgeability follows from these averages.

Exact controls: n=1..3, k=1..4, actual rank-one and invertible sets enumerated by row span; independent count checks; 18 phase families across dimensions including constant, duplicated labels, uneven weights, common row and ranks 2/3. Direct overlap formula vs independent XOR convolution and odd-count spectrum, BigInt cross-products for all inequalities, exact defect, saturation, copy monotonicity and k-linear upper bound. Output decimal ratios only for display. Frozen 72 cases, 144 spectral comparisons. No hardware results claimed.

## QOBS-03: future transfer gates

* Formalize the full convolution and pure-state operational bridge, including equality support and copy monotonicity; test mixed-state dimension dependence and nonuniform shift distributions.
* Compare known-pair discrimination with hidden-X ensemble discrimination. Include a completely readable orthogonal encoding (counterexample to security inferred solely from the ratio), and a constant encoding (zero denominator).
* Define adversary access precisely before transferring anything to oracle lower bounds: classical input versus coherent query, number of copies, secret/public encoding, distribution of challenge, success criterion. Need a reduction to a cryptographic game; no extrapolation from rank shifts to generic cryptographic hardness.

## Quantum Bitcoin / Cryptomania design gates

QBTC-01: define a spend authorization game binding transaction digest, outpoint, chain/network domain, sighash semantics and authorization key; repeated signing, replay, chosen-message queries, key loss and state exhaustion are explicit. Classical deterministic consensus verification is a design target; quantum verification requires a distinct consensus model. No candidate signature construction is proposed here.

QBTC-02: inventory Bitcoin Schnorr/ECDSA, hash commitments, BitVM3 challenge authorization, Nova commitment assumptions, Ark and DLC dependencies in conventional, Shor-capable, and oracle-relative classical-complexity-collapse worlds. Treat any oracle-relative primitive as a conditional interface, not a deployable Bitcoin primitive. Existing classical elliptic-curve authorization and discrete-log-based commitments need replacement in a Shor-capable world.

QBTC-03: build a toy phase-state authorization/discrimination harness with explicit attack games and negative controls, using classical simulation first. Separate cryptographic security, verifier consensus and physical quantum memory costs. Do not represent the observer ratio as a hardness or unforgeability certificate.

## Reproduction

node research/CRYPT_VP/phase_check.mjs
Native workflow: CRYPT-VP quantum observer (separate from historical VPVNP workflows).
