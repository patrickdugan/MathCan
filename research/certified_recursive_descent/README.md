# CRD-01 | Certified recursive descent
2026-11-26. Research note and synthetic benchmark. Status: conditional mathematics plus bounded computation, not a reproduction of the Cogentic theorem.

## Provenance and scope

Primary source: [Cogentic integer factorization README](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/integer_factorization/README.md), pinned at 4a7bc8ab0bc770e71a259b7966c500496b99010a. It claims zero-error expected time L_N[1/3,105], deterministic workspace L_N[1/3,40], and a forthcoming Lean formalization. The PDF was not successfully retrieved as readable content. The phase constant 21.15 and induction ledger 104, 82.56, 103.71 come from a [secondary numerical audit](https://www.solosoft.dev/post/cogentic-factoring-105-constant-audit/). They are treated here as inputs, not verified paper lemmas. Compare [Lee–Venkatesan, 2018](https://arxiv.org/abs/1805.08873), whose randomized NFS analysis concerns square congruence generation.

## A conditional asymptotic closure theorem

Let Lambda(n) = (ln n)^(1/3) (ln ln n)^(2/3) for n >= 3; set Lambda(2)=0. Suppose T(n) is finite and positive for all integer n >= 2, a >= 0, K > 0, and for every epsilon > 0 there is a threshold beyond which

    T(n) <= K exp((a+epsilon) Lambda(n)) [1 + max_{2 <= m <= sqrt(n)} T(m)].

Then limsup ln(max(1,T(n)))/Lambda(n) <= a/(1-2^(-1/3)).

Proof. For n sufficiently large, monotonicity gives Lambda(m) <= r Lambda(n) for m <= sqrt(n), with r=2^(-1/3), since ln ln sqrt(n)=ln ln n-ln 2. Choose C > a/(1-r) and epsilon > 0 with delta=C(1-r)-a-epsilon > 0. Choose a threshold beyond which 2K <= exp(delta Lambda(n)). Let M >= 1 be large enough to cover all finite base values T(m) <= M exp(C Lambda(m)). Strong induction gives

    T(n) <= 2 K M exp((a+epsilon+r C) Lambda(n))
         <= M exp(C Lambda(n)).

Take the limsup, then let C decrease to a/(1-r). QED.

The same argument works with exponent alpha in (0,1) and child sizes <= n^beta for 0 < beta < 1, yielding contraction beta^alpha. The multiplication by the phase bound must already include all recursive calls, including unsuccessful attempts, plus other work. A purely additive recurrence has different constant accounting.

For the reported a=21.15, the fixed point is 102.52086245440401. The explicit rational upper bound r < 3969/5000 follows from 2*3969^3 > 5000^3. Thus 104*r < 82.56, and 21.15+82.56=103.71 < 104. These exact inequalities are checked in audit.mjs. The paper's total constant 105 requires its own complete proof. The workspace claim is separate: depth-first reuse and live data sizes need independent bounds.

## Retry theorem and square-congruence obstruction

Let tau be the first successful attempt, and suppose every history of failed attempts has conditional success probability >= p > 0 and conditional expected next-attempt cost <= H (including failure). Then P(tau >= j) <= (1-p)^(j-1); summing nonnegative costs by conditional expectation yields E(total cost) <= H/p and almost-sure termination. Independence is unnecessary. A marginal success probability alone is inadequate: a hidden fair bit which decides whether every attempt succeeds or every attempt fails gives marginal probability 1/2 but infinite expected stopping time.

For odd n and units x,y with x^2 = y^2 mod n, let g=gcd(x-y,n), h=gcd(x+y,n). Each prime-power component divides exactly one of x-y or x+y, because their common divisor with n divides 2y and hence is 1. Therefore gh=n and gcd(g,h)=1. The square congruence yields a proper factor iff x is not congruent to either y or -y. CRT gives 2^k roots relative to a fixed unit y, where k is the number of distinct prime divisors of n; under uniform sampling the nontrivial fraction is 1-2^(1-k). Without a sampling theorem, this fraction is not a success-probability bound. Prime powers require separate treatment.

The bounded audit enumerates units for every odd composite modulus 9 through 127 and checks all congruent pairs. These computations test the exact finite invariant, not the distribution of an NFS sampler or the claimed algorithm.

## CRD-01 gym: rational proof certificates

Each instance contains pNum/pDen (child log-size exponent), rNum/rDen (proposed upper bound for its cube root), a and c in common hundredth units. The verifier returns:
* domain: invalid parameters;
* contraction: r^3 < p;
* slack: a + c*r >= c;
* valid: both inequalities hold strictly where required.

The data generator uses 336 matched triplets. Each valid certificate has a one-unit phase-cost perturbation that fails slack and a one-unit contraction perturbation that fails the cube-root bound. All three retain the same c; the contraction pair retains the same a. No zero-cost marker is used. Families pDen in {7,11,13} are development, {17} validation, {19,23} held out. This is a synthetic arithmetic task; it does not establish model generalization. The generator emits labels and pair IDs for evaluation only; remove them from observations, shuffle within each split, and fit all normalization exclusively on development. Do not let the model see the emitted order. Keep matched groups intact when bootstrapping.

Run with Node:

    node research/certified_recursive_descent/audit.mjs
    node research/certified_recursive_descent/audit.mjs --dataset > /tmp/crd01.jsonl

## Prospective model protocol

Compare fixed-depth TRM, recurrent TRM with verifier feedback, and recurrent TRM with a bounded candidate bank (BPD-style routing). Start with exact rule-based arithmetic as the reference oracle, random order and single-path heuristics as search baselines. Add a second task where each root offers a bank of candidate transformations and a constrained cost budget; seal this task before comparing trained policies. The current certificate task is classification, so it does not measure search benefit by itself.

Use matched roots, verifier-call budget and training-update budget; report valid certificates accepted, false accepts, rejection-reason accuracy, wall-clock cost and peak resident memory. Candidate retention and selection must count rejected/duplicate proposals and the cost of evaluating them. Train only on development. Select hyperparameters on validation once; open held-out once per registered configuration. Report paired uncertainty at the root/group level. No trained model results yet.

## Follow-up proof audit

1. Retrieve the actual PDF and forthcoming Lean project; pin hashes and compile with its specified toolchain. Inspect axiom dependencies and theorem statements.
2. Extract exact definitions and theorem references for smoothness, sampling, recursive argument size, and trial budget. Distinguish auxiliary residue cofactors from factors of N; two arbitrary factors of N do not both have to be <= sqrt(N).
3. Establish conditional probability of nontrivial CRT sign patterns, or a replacement extraction argument; account for nonunits and prime powers separately.
4. Check retry costs and all recursive multiplicities, base thresholds, bit complexity, and deterministic peak workspace.
5. For ECDLP and Semaev research, treat relation production, independent rank, and certificate verification as separate obligations. No transfer of the factoring exponent to elliptic-curve discrete logs follows from this note.

## Lean scope

Ledger.lean is an isolated Lean 4 candidate checking finite integer inequalities. Run lake env lean research/certified_recursive_descent/Ledger.lean from the repository root. It is not imported into the default build. No Lean executable was available in the execution environment, so compilation remains pending. The asymptotic and probabilistic lemmas above are mathematical derivations, not Lean-checked theorems.
