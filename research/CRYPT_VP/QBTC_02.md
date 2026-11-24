# QBTC-02: public verifier collapse and consensus split

Date: 2026-11-24. Prospective research. QBTC-01 exact-authorization and exact-phase jobs passed on 0edc53fa5e842aff6e713af15534fa7cf69a0873, run 45403072377 (jobs 138476530600 and 138476531188); native replay was still running at inspection. QOBS-01/02 previously passed both jobs on f2bf1d14eb3978dd7b5433e0eee5eba24da3f119, run 45395936583. New QBTC-02 results: local exact enumeration passed; independent CI pending. Written complexity argument, not a Lean-certified complexity theorem.

## Randomized classical public verification barrier

Fix classical oracle O and classical public input x (security parameter, key, fresh signable message, ledger context). Let V^O(x,s;r) be polynomial-time randomized classical verification with polynomially bounded classical witness s, polynomially many independent uniform random bits r, and no secret verification information. Assume some honest evidence s has acceptance probability p(x,s)>=2/3 (or honest average >=2/3, which implies existence). Assume P^O=NP^O in the same classical access model.

Claim: a uniform polynomial-time classical adversary relative to O can find evidence with acceptance probability >1/3, for any such public x. In particular standard negligible unforgeability is impossible. If variable lengths are allowed, encode canonical length and padding with a polynomial bound; reject malformed witnesses.

Proof: amplify V by independent repetitions and majority to A, with p>=2/3 implying acceptance density >=1-epsilon, and p<=1/3 implying density <=epsilon. If A uses m random bits, choose a polynomial repetition count and padding so m>=1 and epsilon<min(1/2,1/(m+1)); exponential error reduction dominates polynomial random-bit growth. Write S_{x,s} subset F_2^m for accepting coins of A. Define the TOTAL classical language R(x,s) to hold if there are m+1 translations t_i with union_i(S_{x,s}+t_i)=F_2^m. This is an existential-universal predicate with polynomial deterministic oracle evaluation, hence in Sigma_2^{P,O}.

For high p, independent uniform translations leave at most 2^m epsilon^(m+1)<1 uncovered points in expectation, so a cover exists. For low p, any union has density <=(m+1)epsilon<1, so no cover exists. Intermediate p is allowed, with R either true or false. Under P^O=NP^O the relativized polynomial hierarchy collapses and R is in P^O. An honest witness satisfies R. The prefix-existence search of QBTC-01 over R uses polynomial time under the same collapse. Its output satisfies R, hence p>1/3. An independent verification attempt accepts with nonnegligible probability. The argument is a promise-gap separator made total by an explicit covering predicate; it does not assume exact acceptance-probability counting or that every candidate has a promise gap. It also works for the final amplified randomized verifier considered as the public predicate in its own right, when it meets the stated completeness premise.

Reference: Sipser-Gacs-Lautemann, BPP subset Sigma_2^P intersect Pi_2^P; covering proof exposition https://www.cs.sjsu.edu/faculty/pollett/254.1.17s/Lec20170426.html. Oracle motivation: Kretschmer, Qian, Tal, https://arxiv.org/abs/2411.02554 (classical oracle, quantum-computable primitives, classical communication). Neither reference claims the Bitcoin application presented here.

## Quantum public verification and consensus

For a fixed classical evidence string and context, let a public quantum verifier independently run from fresh initialized registers, accept with probability p, and emit a classical bit. Classical evidence can be copied; this model assumes any quantum resource needed for verification can be recreated independently with identical parameters. If an odd number t of trials is combined by majority, a_t(p)=sum_{j>(t/2)} binom(t,j) p^j(1-p)^(t-j). For N honest validators using independent randomness, probability of at least one acceptance and at least one rejection is

S_N(a)=1-a^N-(1-a)^N.

At p=1/2 every odd majority is exactly unbiased, so S_N=1-2^(1-N), independent of t. A security proof for typical honest signatures and adversary success does not by itself specify how all possible evidence strings are classified, particularly strings in an acceptance-probability gap. This is a conditional stress test; it does not show that any given quantum signature scheme has an efficiently reachable midpoint string.

If every reachable evidence string has a common intended bit and a uniform per-validator error <=epsilon after amplification, then probability of any wrong verdict across N validators and T attempted checks is <=NT epsilon (conditional bound per adaptive attempt suffices; independence is not needed for this union bound). This is a finite probabilistic agreement bound, not deterministic Bitcoin consensus. For p<=1/2-delta or >=1/2+delta, Hoeffding bounds majority error by exp(-2t delta^2) under independence. A protocol needs a global gap guarantee or a defined resolution mechanism for arbitrary submitted evidence, including malformed strings; an honest-case gap is insufficient. Reorgs, fresh ancilla preparation, physical calibration, and adaptive grinding require separate accounting. If the verifier has an irreplaceable quantum key or receives quantum evidence, independent identical verification cannot be assumed.

## Architecture gates

A. Shor-capable world with retained classical post-quantum hardness: classical deterministic consensus remains a viable target; actual scheme, Bitcoin changes, and proof backend assumptions need audit.

B. P^O=NP^O quantum Cryptomania: quantum-computable verification of classical evidence is not covered by the classical collapse lemma. Public reproducibility, gap and consensus policy are open. A deterministic classical simulation or even an efficient classical bounded-gap separator in the same access model, if available for all witness inputs, would restore the collapse barrier.

C. Quantum verification keys or quantum evidence: introduces physical availability, state distribution, consumption, fork/reorg replay and validator membership obligations. Treat as a distinct ledger design.

D. Classical proof wrappers: if final authorization is a polynomial-size classical witness with a public polynomial-time deterministic or randomized verifier, QBTC-01/02 applies regardless of the prover's quantum computations. A proof of the existence of a valid signature is insufficient for provenance if the claim is already true for a fresh message. A trusted attestation, secret verifier, externally imposed access restriction, or a stronger computational assumption changes the model and must be named.

E. Optimistic BitVM-style games: classical on-chain checks may verify a committed classical computation or a dispute transcript. See https://bitvm.org/bitvm.pdf for the original classical optimistic construction. A classical fraud proof is not automatically a proof of an unknown quantum measurement outcome. For a fixed public context with a terminal existential accepting witness, the barrier applies. A genuinely interactive game with future unpredictable challenges needs a strategy-level analysis; existence of a favorable complete transcript does not imply a winning online strategy. Do not infer that all interactive protocols collapse by this argument. Also audit hash commitments, authorization keys, and timeout assumptions separately. No change to BitVM3 or Bitcoin consensus proposed by this note.

## Exact regression

Node script qbtc02_check.mjs enumerates all 256 subsets of F_2^3 and all 64 ordered shift pairs per subset. For two translations, every set of density <=1/4 fails to cover and every set of density >=3/4 covers. Of 182 intermediate sets, 126 cover; this illustrates why the total separator may choose either answer in the gap. 16,384 exact checks.

Independent verifier model: rational p in {0,1/10,1/3,1/2,2/3,9/10,1}, odd repetitions {1,3,5,9,17,33}, nodes {2,5,10}: 126 exact BigInt cases. Check complement symmetry, majority monotonicity, deterministic endpoints, two-node disagreement and midpoint split. For N=10 and t=17, p=1/3 or 2/3 gives split probability ~0.543768; p=1/2 gives 511/512; p=1/10 or 9/10 gives ~0.0001146384. Decimal outputs are display only.

Next gate QBTC-03: read the specific quantum signature construction in KQT and identify verification oracle calls and classical evidence format; seek an actual bounded-gap verifier statement (or explicit obstruction), and quantify consensus costs without pretending that abstract p is an observed device error. Register proof-wrapper and online challenge models separately. No actual quantum signature, security reduction, hardware experiment or deployable ledger is claimed.
