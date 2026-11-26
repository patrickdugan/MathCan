# TRR-07: uniform interpolation rigidity and completed experiment suite

2026-11-25. Strategy V. The representation model uses affine coordinates and a polynomial of bounded total degree in each input pair separately.

## Uniform result

Let E be a smooth elliptic curve over a field of characteristic zero or p>3, and let G=<T> have prime order N>=7. Set S=G\{O}, f_u(O)=u and f_u(P)=x(P) elsewhere. For every assigned value u, the least polynomial degree in each coordinate pair that represents f_u(P+Q) on S x S is

\[
D_{\min}=\lceil N/3\rceil.
\]

The written geometric proof combines the TRR-03 evaluation-space reduction, the checked integral exclusions at 7, 11, 13 and 17, and the uniform argument below for every N>=19. The argument includes arbitrary extension fields. Order five retains the previously classified exceptions. The Lean modules check the stated field-algebra consequences with their geometric premises explicit.

### The degree-eight obstruction

Use short coordinates y^2=x^3+A x+B, write F(X)=X^3+A X+B and J(X)=3X^2+A, and put w=1/Phi(x). At each Q in S, define a_Q by

\[
w(Q+z)=\frac{\lambda_Q}{z}(1+a_Qz+O(z^2)).
\]

The residue identity from TRR-06 makes a lower-degree decoder equivalent to constancy of a_Q^2-Nx(Q). The logarithmic derivative of w(Z+P)/w(Z) gives the addition identity

\[
a_{P+Q}=a_P+a_Q+N\frac{y(Q)-y(P)}{x(Q)-x(P)},
\]

with the tangent value J(x(P))/(2y(P)) when P=Q. The formula applies when P,Q,P+Q are nonidentity subgroup points.

Suppose N is nonzero in the field, and write a_Q^2=N(x(Q)+c). The doubling identity forces every subgroup x-coordinate to be a root of

\[
K(X)=\left[4(6X+3c)F(X)+(N-1)J(X)^2\right]^2
      -64N(X+c)J(X)^2F(X).
\]

This polynomial has degree at most eight. There are (N-1)/2 distinct roots, so N>=19 forces K=0. Its leading coefficient is 9(N-1)(9N-25), where N is interpreted in the value field. The coefficient equations have two cases:

* If N=1 in the field, they force A=-3c^2/4 and B=c^3/4, hence 4A^3+27B^2=0.
* If 9N=25, characteristic five contradicts N!=0. In the remaining characteristics the next coefficients force c=A=B=0.

Both give a singular cubic. If p=N, the logarithmic cocycle is additive and its coefficient at T is nonzero. Then a_(2T)=2a_T contradicts constancy of a_Q^2, since 3a_T^2!=0. This is the matching-characteristic argument of TRR-06.

The complete proof, the exact coefficient identities, and an independent review are stored alongside the experiment code. The root count uses the subgroup order as an integer; field equalities involving N use its image in the coefficient field.

## Executed finite experiments

| Dataset | Smooth equations | Subgroup instances | Direct matrix checks | Observed degree drops |
|---|---:|---:|---:|---|
| All short equations over primes 5 through 101 | 74,828 | 70,652 | 42,498 | 290 at order five |
| All short equations over F25 and F49 | 2,952 | 2,552 | 1,718 | 24 at order five |
| Seeded cohorts in 26 extension fields | 351 | 444 | 310 | 0 |

Every tested subgroup is checked with a second generator. The first dataset contains 2,380 field-isomorphism classes of equations; the second contains 160. These counts distinguish model multiplicity from isomorphism classes. The sampled extension cohorts reach q=50,653 and include orders 19, 23, 29 and 31. They test prime-order subgroups through 127 and record 95 omitted curve/prime-factor occurrences above that cap. Sampled F25/F49 cohorts overlap their exhaustive datasets, so the rows should not be added as disjoint coverage.

Each field receipt records its defining polynomial, coefficient sampling rule, seed, subgroup generator, signed Frobenius orbit, ordinary/supersingular status, special j-invariant and full/proper subgroup status. Known order-five controls include parameters outside the prime field. Direct matrix checks derive the evaluation hyperplane from monomials independently of the residue formula.

## Robustness and representation controls

`robustness.py` computes exact function distances on 32 fixtures. The value at O is free; Hamming cost counts changes on S. It exhausts the admissible function space after quotienting by constants, and independently verifies the resulting witnesses in the monomial evaluation space.

Most fixtures require N-3 changed function values. The order-five positive control needs zero. An order-11 subgroup on y^2=x^3+x+5 over F23 has distance six, with a three-dimensional admissible function space. The complete curve, subgroup and witness are recorded in `results/robustness.json`.

For arbitrary table changes on S x S, diagonal correction produces a lower-degree decoder with at most N-1 changed cells. Each corrected table is verified directly. The sampled corrected tables fail translation consistency, which explains why the two Hamming metrics give different results. Eight random even functions and one arbitrary symmetric matrix per fixture calibrate the tests. Rational addition and repeated-squaring controls record their exact identities and operation counts.

## Certificate and proof checks

* The unchanged TRR-05 certificate passes all 83 checks, and ten corrupted proof inputs are rejected.
* The generic chart and local-series audit passes 32 symbolic checks.
* The direct verifier reconstructs the chart, H and lambda and replays the certificates at orders 19 and 23. Six focused guard controls pass against the order-19 certificate.
* The FLINT verifier reconstructs the local Laurent coefficients from the kernel polynomial, checks their integer identities with the stored residue equations, then recomputes every norm, the integer Bezout identity and all exceptional fibres. It uses the written residue identity. Nine corrupted elimination inputs and two corrupted residue equations are rejected. `replay_review.md` explains the proof and the denominator checks.
* Lean checks 15 field-algebra lemmas: nine in the initial module and six in the uniform coefficient argument. Both modules declare no extra axioms and admit no goals. The proof receipts identify their sources and explicit premises.

The geometric prerequisites remain written proofs: invariant differentials and residues, Riemann-Roch, the genus-one principal-divisor criterion, the differential kernel over perfect constants and chart coverage. The formal receipts state this boundary explicitly.

## Additional integral certificates

The bounded symbolic searches produced the following sufficient elimination integers. Each candidate characteristic receives a complete residue-field factorization and a fibre-gcd test against a power of the discriminant. The search receipts include the earlier memory failures and the smaller lattice that resolved them. The independent replay status is recorded separately, so generating a certificate cannot by itself mark its verification complete.

| Order | Algebra rank | Residual norm degree | Sufficient integer | Candidate characteristics above three |
|---:|---:|---:|---|---|
| 19 | 6 | 30 | 61,731 = 3^2 * 19^3 | 19 |
| 23 | 9 | 44 | 110,817,036 = 2^2 * 3^2 * 11 * 23^4 | 11, 23 |
| 29 | 14 | 70 | 15,506,428,644 = 2^2 * 3^3 * 7 * 29^5 | 7, 29 |
| 31 | 16 | 80 | 46,379,224,620 = 2^2 * 3^4 * 5 * 31^5 | 5, 31 |

The order-23 certificate resolves a characteristic-11 fibre over F_(11^11). Order 29 includes two degree-seven residue fields in characteristic seven. The order-31 characteristic-five fibres require degree-three extensions. Every computed fibre has singular support. These calculations test the geometric theorem across characteristics and extension fields.

The original direct Node replay reached its 600-second limit at order 29 and ended with SIGKILL at order 31. Those attempt receipts are preserved. `flint_replay.py` avoids the large quotient inverses by computing Laurent fractions in the free ring Z[r,t] and reducing only the final integer cross-products modulo the order equation. Complete replay receipts are stored under `receipts/flint_replay*.json`; they bind both verification stages to the same certificate SHA-256.

## Reproduction and CI

The public workflow `.github/workflows/trr07-experiments.yml` runs four finite-field cohorts, the robustness suite, baseline/guard/proof checks, and independent symbolic searches at orders 19, 23, 29 and 31. Every symbolic job has a 900-second search budget and a 768-MiB PARI stack. FLINT replays all four resulting certificates; orders 19 and 23 also receive direct H-lambda replay in Node. The report requires a complete replay receipt with a matching certificate SHA-256. Complete JSONL ledgers, checkpoints and replay logs are retained as CI artifacts for 30 days.

From the repository root:

```sh
python research/translation_rank_rigidity/trr07/finite_sweep.py --prime-max 101 --max-order 0 --output results/prime.json --cases results/prime.jsonl
python research/translation_rank_rigidity/trr07/robustness.py --out results/robustness.json
python research/translation_rank_rigidity/trr07/test_certificate_mutations.py
python research/translation_rank_rigidity/trr07/test_symbolic_guards.py
python research/translation_rank_rigidity/trr07/test_flint_bridge.py
python research/translation_rank_rigidity/trr07/audit_symbolic.py
python research/translation_rank_rigidity/trr07/uniform_probe.py --output results/uniform.json
lake env python research/translation_rank_rigidity/trr07/proof_check.py
lake env python research/translation_rank_rigidity/trr07/proof_check_uniform.py
```

The exact symbolic searches require PARI/cypari2 and python-flint 0.9.0. Their replay uses FLINT and Node 22. SymPy 1.14.0 supports the independent symbolic audits. See `symbolic_README.md`, `receipts/finite_summary.json`, `proof_review.md`, `replay_review.md`, and the uniform proof files for precise inputs and remaining formal obligations.

This theorem classifies the specified interpolation degree. A transfer to a broader computational model requires a separate statement connecting its charged resources to that model.
