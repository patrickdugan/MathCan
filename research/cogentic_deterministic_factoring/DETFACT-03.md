# DETFACT-03: effective relation coverage, polynomial-pair preconditioning

Status: independent constructive polynomial-pair lemma proved and finite replay passed. The effective analytic coverage gate remains open. No claim of a working upstream algExp.

Sources: [pinned Cogentic theorem statements](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/README.md); [independent proof overview, 25 November 2026](https://aiprovedwhat.com/episodes/go02-deterministic-subexponential-factoring/); [independent certificate verifier, Mode 4](https://github.com/lluiseriksson/cogentic-deterministic-factoring-certificates/blob/main/src/detfact_certifier.py). Mode 4 lists finite preconditioning conditions attributed to Lemma 8.1. Those conditions motivated this independent construction. The original 59-page PDF and announced Lean source remain inaccessible to this audit. The construction is not attributed to Cogentic or claimed novel.

## 1. Constructive preconditioning theorem

Assume integer d>=4, integer z>=2, integer m>=4d, odd composite N with (m-1)^d<N<m^d, and prime ell>max(z,d). Write P=product of primes <=z, Q=P*ell; assume gcd(N,Q)=1. Define c=4Q+P/2. There exist two integer polynomials f_1,f_2 of degree d with the following properties:

* Common odd leading coefficient c>=4Q, divisible by P/2 and coprime to ell.
* All lower coefficients lie in [0,Qm).
* f_i(m)=k_i N with 1<=k_i<2c and gcd(k_i,Q)=1.
* Modulo 2 each polynomial is monic irreducible of degree d. At every integer x, f_i(x)=1 mod P.
* Modulo ell, f_1 splits into d distinct simple linear factors; f_2 has no root.

Proof. Choose any monic irreducible polynomial of degree d over F_2 (finite-field existence). For each odd prime dividing P prescribe the constant polynomial 1. Modulo ell prescribe c times a monic product of d distinct linear factors with roots excluding m mod ell; this is possible because ell-1>=d. For f_2 prescribe c times a monic root-free polynomial of degree d. Use powers of an irreducible quadratic for even d, and an irreducible cubic times powers of a quadratic for odd d. These exist over every finite field. Both prescriptions have the leading residue c at every prime dividing Q, and both evaluate nonzero at m in each such field.

Apply coefficient-wise CRT to the lower coefficients, choosing residues R_j in [0,Q), and set R_d=c. Then gcd(R(m),Q)=1. Since N is invertible modulo Q, choose k to be the least integer >=ceil(R(m)/N) satisfying k=R(m)*N^(-1) mod Q. Thus 0<=kN-R(m)<QN, and gcd(k,Q)=1.

The integer H=(kN-R(m))/Q satisfies 0<=H<N<m^d. Take its base-m digits h_j (0<=j<d), and put f(X)=R(X)+Q sum_j h_j X^j. Its evaluation at m equals kN, its coefficients below degree d are <Qm, and all prescribed residue patterns are preserved. Since m>=4d, Bernoulli gives (1-1/m)^d>=1-d/m>=3/4; hence m^d/N<4/3. Also R(m)<(c+Q/(m-1))*m^d. Therefore

    k < R(m)/N + Q
      < (4/3)*(c+Q/(m-1))+Q < 2c,

using Q<=c/4 and m>=16. Positivity follows from c>0. Irreducibility modulo 2 and d>=2 imply both evaluations at 0 and 1 equal 1 mod 2; CRT then gives f_i(x)=1 mod P for every integer x. The split polynomial's roots are simple because its leading coefficient is nonzero and roots distinct. QED.

All finite-field searches may be exhaustive: for binary irreducibility, enumerate monic degree-d polynomials and test divisibility by monic polynomials up to floor(d/2); for the quadratic and cubic enumerate monic coefficients and test roots. This gives crude deterministic costs 2^(O(d)) poly(d) and poly(ell), respectively. CRT and lifting use polynomial bit work in the explicit input and output sizes. This is a construction of the starting pair only. No field discriminant, ideal-generation, or good-pair condition beyond the listed properties is established.

## 2. Perturbation family and coefficient budget

For any g_i of degree <=d-2, define F_i=f_i+Q(X-m)g_i. This preserves the degree, leading coefficient, f_i(m)=k_i N, all residues modulo Q and all root conditions. It can introduce negative lower coefficients, which are allowed in this perturbation family; the original nonnegative digit bound does not persist. If every g_i coefficient is in [-A,A], then absolute lower coefficients of F_i are bounded by Qm+Q(m+1)A.

The map g_i -> F_i is injective since Z[X] is an integral domain. Thus there are exactly T=(2A+1)^(2(d-1)) ordered pairs, including the starting pair. Candidate count alone does not bound total bit complexity. With total relation-search work per candidate bounded by exp(o(L^.75)), L=ln N, and the number of candidate pairs over all target primes bounded by exp((4 ln 2+o(1))*L^.75), their product is within O(exp(3 L^.75)) because 4 ln 2<3. These are conditional cost premises, not recovered parameter choices from the source PDF.

## 3. Effective coverage contract

Let P_target be a finite set of eligible primes ell, with a deterministic indexed family of T pairs per ell. Each pair has a success predicate requiring a verified proper divisor or a positive relation exponent e_ell with ell^e_ell=1 mod N. Failure includes inability to construct or check the relation within the assigned bit budget. If the search returns a divisor it is complete. Otherwise, write F for the total number of failed incidences (ell,pair). Every prime without any certified relation accounts for T failures, so

    #covered primes >= #P_target - floor(F/T).

Thus an effective bound F<=(1-eta)*#P_target*T with fixed eta>0 implies at least eta*#P_target covered primes. When the target supply has size >=c0 B/log B, this meets the density premise of DETFACT-02. A weaker per-prime existence argument could also suffice. The bound must be uniform in N and effective, including any exceptional characters, and count actual failed relation attempts rather than mere violations of an unproven proxy. Counting candidates and establishing a nonempty initial family do not imply this bound.

The independent overview attributes the source proof to polynomial-pair relations and effective Landau-Page / Montgomery zero-density estimates. The following source-specific gates are still unresolved:

1. Pin the exact field family, discriminant bounds and multiplicities from the upstream PDF.
2. Identify the analytic exceptional sets with their conductors and quantify how they map back to pair incidences. A bound on characters alone is insufficient if many candidate pairs share a character or field.
3. Prove the precise algebraic relation-production predicate (including the rank, localized denominators and signs); certify all surviving modular congruences.
4. Establish a uniform effective count of covered target primes and an explicit bound on relation bit widths and total search cost. Do not invoke ineffective Siegel constants.
5. Compose with DETFACT-02 and DETFACT-AUDIT-01; review the announced Lean formalization when released.

Mode 3 of the independent verifier gives a useful local interface: if ell^E P=s1 mod N and P=s2 mod N, both s_i in {+1,-1}, then ell^(2E)=1 mod N. This follows by substitution and squaring. It verifies an already constructed relation, leaving existence, rank and cost open.

## 4. Finite replay

Run node preconditioning_audit.mjs. Synthetic composite N are multiples of 31 constructed inside the base-m bracket with gcd(N,Q)=1. The exact BigInt implementation builds polynomials by CRT and lifting, independently checks each evaluation, bound, finite-field irreducibility, root count and derivative, and verifies perturbed pairs and a small injectivity slice. The receipt was generated by executing the same audit function in the authoring JS runtime; Node was not separately invoked. The tests include deliberate broken evaluations, incorrect root patterns and forged k. These are preconditioning fixtures, not relation searches or factorization experiments.

## 5. Formalization and gym handoff

A tractable next Lean module separates coefficient CRT, bounded base expansion, evaluation preservation, and perturbation injectivity. The finite-field existence and analytic count need separate formal dependencies. MathCan uses Lean 4.35.0; no kernel build is available here. DataGoblin can use small synthetic fixtures with the exact polynomial verifier: provide d,m,N,ell and residue prescriptions, request a bounded lift, or ask the model to diagnose a corrupted pair. Use disjoint parameter families for held-out tests. The effective analytic coverage claim stays pending until the original paper and proof dependencies are available.
