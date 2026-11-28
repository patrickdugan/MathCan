# GRH-C01–06: arithmetic compactification (stage 0, 2026-11-28)

Status: written abstract theorems, exact finite tests, source-level axiom review, and a pending Lean candidate. No independent proof of GRH or transfer theorem to learned recurrent networks is claimed. This extends MathCan RH-01 rather than replacing the original pinned upstream.

## Provenance and interfaces

* Original Alpöge–Claude proof: https://github.com/leanprover-community/riemann-hypothesis (see parent RESEARCH.md for the original pin).
* Readable Lean edition: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh (Apache-2.0). Lean 4.35.0, Mathlib 56a00585 per upstream README. The separate compact edition has the same five statements.
* Ye Yu's Gemini-assisted exposition: https://github.com/sdyy1990/riemann-hypothesis/tree/5edf43ce39c068fec64e0cc122e9cbdcec343b24 (MIT); English markdown blob 7d359f148b243bd3112ae822659b67eac526bfa1, correspondence blob b9f5bbad45f78d88df9a6f27646f229f3c2ac66b. Section 1.3 reproduces the diagram. Treat the exposition as a guide, and formal declarations as the authority for hypotheses.

| ID | Source file under grh/src/New/ and declaration | Pin (blob) |
| --- | --- | --- |
| C01 | UpperBound/Seesaw/SeesawIdentity.lean: seesaw_identity | 4d0a5499ce992297b859168c21408f9ed3b21aba |
| C01,C02,C06 | Reduction/ShortAndEnough.lean: span_short_integralRamified_eq_top, indexLe_normalizedPoincare; divisibilityError, seesawConst | 5cdf6a9a61c20ad5f69e7bd8109d307027833383 |
| C03 | Spanning/SecondMoment/SpanningTheorem.lean: isSpread_goodPoincare; ShortAndEnough.lean: enough_forms | 4b47ff63873e2e0b0a349be79900a1e47e5b1933 |
| C02 | Determinant/Twist/LongForms.lean: integral_forms_long | bc473640e088d1977bf33b0aa377d60540f4e66c |
| C04,C05 | Reduction/MainInequality.lean: star_inequality | 97f83ab52b2feb420e952a2722b4cef454b9e579 |
| C06 | Reduction/OneSidedBound.lean: grh | 99e5240de112527b739068b692e5007720d310c1 |

Theorem A bounds size of short integral images and their shared twisted index; B supplies a small union of translates with rank at least (1-4/b²)d; C applies to an independent tuple of sufficient length and bounds its covolume plus twice the index from below. The source's "m lifts" and arithmetic gains are specific to theta lifts; no assumption that arbitrary repeated learned maps enjoy them is licensed.

## C01: additive divisibility under iterated operators

THEOREM (elementary). For compatible integer matrices A_j with every entry divisible by p^(g_j), write A_j=p^(g_j) B_j, g_j nonnegative integers. Then A_m ... A_1 = p^(sum g_j) B_m ... B_1. Proof by induction and centrality of scalars. Equivalently the minimum entry valuation of a product is at least the sum, with v_p(0)=infinity. If each matrix is square and nonsingular, determinant valuation is exactly additive, since det is multiplicative. Entry valuation and determinant valuation are different invariants. For A=[[1,1],[1,-1]], A²=2I: the p=2 entry valuation gain is strict. This is a divisibility model, not the theta derivative theorem.

The upstream seesaw theorem has one nonzero scalar c chosen before the twists, with a twist-specific chain datum; the expression is not guaranteed nonzero. Source normalization invGainFactor uses a finite product of prime powers with floored gain minus error. Its exact cancellation requires upstream colength, gauge and archimedean hypotheses.

## C02: abstract lattice comparison

THEOREM. Let d,n>0, n<=d; independent vectors have a common logarithmic squared covolume upper bound V<=n(H-R+L). Let delta<=dI, and assume d(H-C)<=V+2delta. Then
 nR <= d(C+I+I)+nL-(d-n)H.
Proof: eliminate V,delta and distribute. If H,L,I,C>=0 and n>=rho*d with rho>0, then R <= (C+L+2I)/rho, treating R<=0 separately. Set C=3L to recover the GRH scalar budget.

Hadamard supplies a V bound from individual squared lengths (Gram determinant <= product of squared norms). For an independent tuple this can be logged. A valid delta requires a common index certificate for the SAME family and relevant local twists; a collection of unrelated denominator bounds is insufficient. Ordinary rational lattices allow finite denominator clearing; their index is not automatically upstream TwistedLattice.IndexLe. The independent arithmetic/geometric lower bound remains a hypothesis.

## C03: spectral coverage and greedy rank

THEOREM (finite-dimensional transfer candidate). Let P_i be orthogonal projectors on a d-dimensional Hilbert space, with weights w_i>=0, sum w_i=1 and sum w_i P_i >= alpha I for alpha>0. Given current span W, let Q project onto W-perp (rank r). The weighted trace sum sum w_i tr(QP_i) >= alpha r. For each i, tr(QP_i)=tr(P_i Q P_i) <= rank(QP_i): the nonzero eigenvalues of P_i Q P_i lie in (0,1], and rank equals the rank of QP_i. That rank equals dim(W+range P_i)-dim W. Thus greedy maximum rank gain is at least alpha r, and residual rank after k steps is at most d(1-alpha)^k. For alpha=1 coverage is immediate. For 0<alpha<1, k>=log(1/eps)/[-log(1-alpha)] suffices for at least (1-eps)d covered dimensions.

Coordinate projector test: all 109 full-support pools of nonempty subsets of a 3-element universe; alpha is the minimum relative coordinate incidence. Rotated rational test: two orthonormal bases in R², one built from (3,4)/5,(-4,3)/5; average projector is I/2. Exact rational rank gives finite certificates. Repeating only the e1 projector cannot cover e2. Upstream IsSpread is a distinct theorem, with large-sieve and multiplicity estimates; the average-projector hypothesis must be separately established for any transfer.

## C04: exact global cancellation and the coverage penalty

For C=3L, exact comparison reads
 nR <= d(4L+2I)-(d-n)(H+L).
This is algebraically equivalent to the source comparison after covolume/index bounds. With rho=n/d, divide by n:
 R <= (4L+2I)/rho - ((1-rho)/rho)*(H+L).
The source discards the nonpositive coverage term (H>=0, L>=0), then uses rho>=1/2 and the prescribed scales. This sharper expression is a conditional corollary, not a stronger prime theorem without the source's parameter analysis.

Control witnesses: d=2,n=1,H=-10,L=I=0,R=10 violates the relaxed conclusion when H>=0 is omitted. d=n=1,H=L=0,I=1,R=2 demonstrates why the coefficient 2 cannot be replaced with 1 in the scalar premises. d=1,n=0,H=I=0,L=1 allows arbitrary R. These are scalar countermodels to invalid relaxations; they need not arise from admissible arithmetic data.

## C05: repeated-operator budgets

If R=sum_j r_j, L=sum_j ell_j, C=sum_j c_j, and I is a shared index budget, the preceding theorem gives
 (sum_j r_j)/m <= (sum_j (ell_j+c_j)+2I)/(rho*m)
for m>0, positive coverage, nonnegative costs and the SAME global comparison. Thus a fixed index cost amortizes across depth under these hypotheses. A depth-linear loss leaves an average floor; rapidly falling coverage can destroy the bound. Noncommutative normalized chains must preserve order. The finite chain experiment checks exact scalar normalization and additive valuation gains; it does not supply a learned-model or analytic remainder bound.

## C06: constructivity and proof dependency audit

Source-level evidence: readable ShortAndEnough is noncomputable and selects divisibilityError and seesawConst from existence proofs. The latter is chosen with uniformity over twists. MainInequality selects a finite independent tuple from a spanning union. LongForms selects regular twists and auxiliary forms; its lower bound depends on the family assumptions. Upstream top-level PrintAxioms.lean enumerates the five exported theorems; the upstream README reports propext, Classical.choice, Quot.sound. This session did not rerun an independent Lean kernel or extract transitive proof terms. A choice occurrence is a proof-audit target; it neither proves essentiality nor supplies an elimination algorithm. No reduction in axioms is claimed.

Finite substitute: greedy exact rank extraction from a presented rational matrix gives explicit independent columns/rows; multiply by a common product of presented denominators to clear them. This is effective, and 256 small witness problems pass. It does not construct admissible data, unbounded twists, or the automorphic existence witnesses. Separate input enumeration, termination bounds, algebraic effectivity and transitive axiom dependencies in the next stage.

## Reproduce and next gates

Run node research/rh_proof_distillation/grh_c/pilot.mjs and compare receipt.json. Standard Node, CPU-only, exact BigInt, deterministic, no API calls. The checked-in receipt was produced by running the same campaign function in the session's JavaScript engine. No Lean executable was available locally. Compactification.lean is an isolated Mathlib candidate; the root MathCan lake project is Init-only. Check it in a compatible pinned Mathlib project with lake env lean /absolute/path/to/Compactification.lean and inspect #print axioms before marking LEAN-CHECKED.

Next stages: (1) run the native scalar proof gate, (2) prove the projector lemma in Lean and check noncommuting frame families, (3) extract actual proof-term dependencies, index composition and choice sites from the pinned compiled GRH cache, (4) test the sharper bound under real admissibility scales without circular GRH assumptions, (5) compare the spectral coverage hypothesis on actual compactification workloads against matched random/redundant/operator-order controls. Stop if the required common index, lower bound, or uniform spectral gap fails.
