# VPVNP-BGS-01: relativization and existential rank barriers

2026-11-24. Companion to MathCan PR #273, deliberately on a separate branch from main so the completed observer and countable-gauge gates are not disturbed. No new unconditional Boolean complexity separation is claimed.

## Source contract

* Baker, Gill, Solovay, [Relativizations of the P =? NP Question](https://doi.org/10.1137/0204037), 1975: recursive oracles A,B with P^A=NP^A and P^B!=NP^B. This excludes fully relativizing arguments for either answer, not every argument ending with a diagonalization.
* Williams, [Nonuniform ACC Circuit Lower Bounds](https://doi.org/10.1145/2559903), 2014: a faster restricted circuit-SAT algorithm plus a hierarchy argument yields NEXP not in ACC/poly. It does not settle P vs NP.
* [Anthropic source](https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp), [OpenAI manuscript](https://github.com/openai/math/blob/main/preprints/VP-and-VNP-are-different-November-23-2026/build/Paper.tex). The formal polynomial semantics and the algebraic wire model are crucial. Compare the two hinges without assuming equivalence.
* Prior [MathCan native audit](https://github.com/patrickdugan/MathCan/actions/runs/45387078704) and [countable-gauge upstream audit](https://github.com/patrickdugan/MathCan/actions/runs/45387078667) at b3b3c16 both passed. These are algebraic/Euclidean results.

## BGS-01A. Exact existential rank blowup (written proof)

Fix n and a field K. Index rows and columns by all subsets x,y of [n]. Put D_xy=1 if x and y are disjoint, 0 otherwise; O=J-D is nondisjointness; C_xy=|x intersect y| in K. The witness matrices W_i(x,y)=1_{i in x}1_{i in y} have rank one. C=sum W_i has rank n: upper bound by factorization through K^n, lower bound from the singleton-by-singleton identity submatrix.

Let Z_xy=1 if y subset x. Z is invertible, since a size-refining ordering makes it triangular with diagonal 1. D=Z diag((-1)^|t|) Z^T follows from the binomial identity on x intersect y. O=Z diag(d_t) Z^T with d_empty=0, d_t=(-1)^(|t|+1) for nonempty t. Consequently rank(D)=2^n and rank(O)=2^n-1 in every characteristic. This is a sharp exponential gap between arithmetic addition and Boolean union, even for rank-one witness matrices and a linear-size circuit. It does not imply a lower bound for unrestricted Boolean circuit size.

Alternative native proof target: D is the n-fold Kronecker power of [[1,1],[1,0]], with explicit inverse the n-fold Kronecker power of [[0,1],[1,-1]]. If z is the empty set index, D has an all-one row and column at z. Put E_ij=1_{i=z}, P=E-I. Then O=DP. D has full rank and P has a zero z-column and a (-I) submatrix off z. Hence rank(O)=2^n-1. BooleanOracle.lean formalizes this route and the query theorem below; native CI pending.

## BGS-01B. Oracle transcript lower bound (written proof)

Let an unknown function o:{0,1}^n->{0,1} be accessed via point queries only. The problem is OR(o)=exists x:o(x)=1. A nondeterministic verifier guesses x and queries once, paying n bits of witness and query writing in the oracle TM model. A deterministic adaptive query tree that correctly computes OR on all-zero and all one-hot oracles must query every one of the 2^n points on its all-zero path. Otherwise the one-hot oracle at an omitted point induces the same transcript and output. This proof covers adaptive trees and repeated queries. It yields a finite query-complexity theorem, not BGS's whole asymptotic recursive-oracle construction.

Randomized extension: under an equal mixture of all-zero and a uniformly chosen one-hot oracle, a deterministic tree of query depth q has success at most 1/2+q/(2*2^n), by the same indistinguishability argument. Averaging over random seeds proves the bound for randomized q-query algorithms under this fixed distribution. Worst-case success >=2/3 requires q>=2^n/3. Quantum query complexity is a separate model (Grover speedup does not supply a classical replay algorithm).

Oracle semantics matter. A batch OR oracle or a PSPACE-complete oracle can answer existential questions at much lower oracle-query cost than point access. In standard relativization the same oracle is shared by all machines; do not change the oracle per instance when making an asymptotic separation claim. Oracle gates in a placed network still obey cut-rank bounds if all their inputs physically cross the cut and are counted. The failure is any resource model that assumes efficient local arithmetic representations or permits uncharged distributed query dependencies. Distinguish the internal gate cost, arity, wire cost, and query communication.

## BGS-01C. Bounded ambiguity restores a polynomial rank overhead (written proof)

For 0/1 matrices W_1,...,W_m, entrywise Boolean union O has the exact inclusion-exclusion expansion
O = sum over nonempty S subset [m] of (-1)^(|S|+1) HadamardProduct_{i in S} W_i.
Writing each W_i as a sum of r_i rank-one outer products shows rank of a Hadamard product is at most product r_i, by distributing the products. Therefore rank(O) <= product_i(1+r_i)-1, tight for the singleton witness example.

If every entry has at most d active witnesses, every term of size >d is identically zero. Thus
rank(O) <= sum_{1<=|S|<=d} product_{i in S} r_i.
For fixed d and rank bound r_i<=r, the overhead is O((mr)^d) (r>=1), valid over every field, including F_2. For d=1 the Boolean existence matrix is exactly the sum. This suggests a restricted transport theorem for verifiers of bounded ambiguity under a fixed bipartite flattening. It alone does not turn an NP language into a small formal arithmetic circuit: the number of witness choices may be exponential, and rank decompositions across one cut need not yield a globally efficient circuit.

Sharpness: restrict rows and columns of BGS-01A to subsets of cardinality <=d. The restricted zeta matrix is still square triangular with unit diagonal; the same factorization yields rank(O)=sum_{k=1}^d binom(n,k), rank(C)=n for 1<=d<=n. This proves the order of the rank blowup cannot be improved uniformly for rank-one witness matrices. For p<=d a count may vanish modulo p while existence is true. In characteristic zero or p>d, a univariate polynomial 1-product_{j=1}^d(1-C/j) computes existence on counts 0..d; the inclusion-exclusion form avoids division and is characteristic independent.

## Cross-proof audit

| Ingredient | Transfer condition | Negative control / gate |
|---|---|---|
| Spectral prices | Define tensor object, semiring/field, restriction and cover relation with monotonicity and multiplicativity | Boolean OR is not arithmetic cover addition; A proves unbounded ambiguity blowup |
| Flat obstruction | Valid local cost and cut-rank upper bounds under the exact chosen semantics | Nondisjointness is easy as a circuit despite high rank across one cut |
| Contracting accelerator | Uniform speedup for a structurally described circuit class with explicit gate/bit cost | B proves no generic subexhaustive point-oracle OR algorithm |
| Recursive replay | Simulation of all allowed programs and circuit descriptions under the budget, with witness handling and arbitrary nonuniform advice accounted for | Query transcript and count cancellations; no assumption that arbitrary circuit truth tables have short multilinear circuits |
| Relativization | Specify oracle interface and identify which proof hypothesis fails, rather than only naming a nonrelativizing technique | BGS's equality oracle rules out an all-oracle separation |
| Indirect diagonalization | Apply a correct hierarchy or algorithms-to-lower-bounds theorem with matching uniformity, class, and runtime | NEXP vs ACC does not settle NP vs P/poly or P vs NP |

Do not assume that even a deterministic SAT decision algorithm gives a polynomial-size formal circuit for arbitrary #P witness polynomials. Distinguish Boolean equality, formal polynomial identity, counting, and existence. A proposed unrestricted Boolean lower bound must also address natural-proofs and algebrization barriers where applicable. This branch has no claim to escape them.

## Local receipt

Executed deterministic exact JS regression (seed 20261124 for 640 pair-union controls), fields 2,3,5,7,11. 30 rank triples (n=1..6); 27,300 coefficient-free inclusion-exclusion entry checks; 11 positive count cancellation examples; 640 general two-matrix OR upper-bound checks; 6,058 all-zero-path/one-hot combinations (all paths of length up to N for N=2,4 and up to 3 for N=8); 276 complete small OR truth-table scans (N=2,4,8); 90 bounded-ambiguity rank cases (n=1..7,d<=3) and 43,975 truncated identity entries. Finite data are regression evidence for the written proofs and are not novel asymptotic lower bounds. The OR-path pilot enumerates paths rather than all adaptive trees; the written and Lean proofs handle arbitrary finite adaptive trees.

Replay: node research/VPVNP_BGS/bgs01.mjs.
Native: copy BooleanOracle.lean to experiments/deligne_mathlib and lake env lean BooleanOracle.lean. Axiom allowlist: propext, Classical.choice, Quot.sound. Twelve named targets; native status pending.

## Continuation ledger

1. Repair native elaboration against pinned Mathlib, without weakening statements. Require all twelve axiom reports and exact receipt.
2. Formalize finite Hadamard-rank factorization and bounded-ambiguity union theorem; prove tightness by the restricted zeta factorization. Register cut-wise and globally consistent tensor-cover variants separately.
3. Formalize randomized transcript lower bound (distribution over deterministic trees) and lift deterministic query argument to a clocked oracle TM diagonalization with finite staged oracle construction; explicitly preserve prior stages.
4. Test structured SAT speedups with finite witness ambiguity, affine constraints, bounded treewidth and bounded cutwidth, including point-oracle adversaries and equal resource accounting. A Boolean circuit-SAT improvement must be established as a uniform algorithm with a stated asymptotic bound before invoking a Williams-type theorem.
5. Define a candidate Boolean spectral price only after specifying the allowed witness-composition operation. Audit the new predicate against the classical BGS oracles and against the two source proof interfaces. Preserve negative findings.

Tail prompt: Continue VPVNP-BGS-01 from the committed ledger. Inspect native/exact CI, repair the first failing gate, then develop the bounded-ambiguity Hadamard-rank theorem and randomized query obstruction. Keep the full oracle theorem distinct from finite models; record every proof obligation and never infer P != NP from the algebraic separation.
