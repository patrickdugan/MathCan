# Strategy V prospectus: uniform translation-interpolation rigidity

Update 2026-11-26: [TRR-11](../trr11/README.md) completes the tame,
large-order theorem for generalized Weierstrass coordinates in Lean.
[TRR-12](../trr12/ECDSA_RISK_ASSESSMENT.md) supplies the ECDSA risk
assessment and the next evaluation contract. Its checked O(log q)-gate
decoder makes the difference between ordinary degree and evaluation cost
explicit. The security-facing next task is a cost-preserving reduction
for a specified recovery candidate; the original order-by-order experiment
plan below is retained as research history.

Update 2026-11-25: [TRR-07](../trr07/README.md) executes the bounded experiment program and supplies a uniform written proof for every prime order N>=19. Together with the existing small-order certificates, this proves the exact interpolation degree for every prime N>=7 in the specified characteristic range. The coefficient classification is checked in Lean; the geometric foundations remain written proofs. The original prospectus below records the earlier decision and acceptance gates. Broader computational implications require a separate transfer theorem.

Original status: strong candidate for a uniform restricted-model theorem. The research goal is to understand the geometry of a translation-coordinate evaluation obstruction, within the existing toy-only scope.

## What is established

TRR-03 bounds the affine-block degree between floor(N/3) and ceil(N/3). TRR-05 excludes the lower value at primes 7,11,13,17 over all fields of characteristic >3, using checked integral identities. Order 5 is a positive exceptional control. TRR-06 derives a uniform residue identity and excludes the matching characteristic N=p (written proof, pending formalization). These results only sharpen the existing degree bound by one, so the asymptotic degree remains Theta(N). The scientific opportunity is a uniform explanation of the zero locus and whether it controls other precisely defined representation models. Neither high degree nor high matrix rank implies general circuit complexity or a discrete-logarithm lower bound; rational coordinate addition and repeated squaring are explicit controls.

## Conjecture and falsifier

For every prime N>=7 and every smooth curve with a rational marked point of order N in characteristic >3, the quantities a_Q^2-N x(Q) cannot be constant on G minus O, where a_Q is the regular coefficient of the normalized logarithmic expansion of w=1/Phi(x) at Q. A single exact smooth counterexample, with all denominators checked and direct evaluation-space containment verified, falsifies the conjecture. Matching characteristic is discharged by TRR-06 subject to its proof obligations. No claim of novelty relative to the algebraic geometry literature until reviewed.

## Original empirical program and acceptance gates

| Stage | Dataset / method | Acceptance gate |
|---|---|---|
| V-E1 | Reproduce original 83 checks on public CI; independently check generic chart identities; mutate a cofactor and residue numerator. | Baseline passes; each corruption rejected. |
| V-E2 | Toy prime orders 19,23,29,31; use exact modular-curve equations and reduced residue ratios; require saturated integral certificate. | For every p dividing certificate integer, resolve all fibres over algebraic closures; separate unfinished from certified. |
| V-E3 | Enumerate small fields p<=101 and selected finite extensions with q<=2^16; stratify p=N, tame split/non-split, j=0,1728, ordinary/supersingular, full/proper subgroups. For larger toy fields sample fixed seeded cohorts. | Record counts by stratum, including failures/timeouts. Direct matrix containment agrees with residue test for every small case and each candidate. Never treat zero observed exceptions as a theorem. |
| V-E4 | On the moduli curve, compare common zeros of a_Q^2-N x(Q) differences with singular fibres. Record support and multiplicity of residual norms, prime factors of sufficient certificate integers, degrees, coefficient heights, and timings. | Derive a uniform algebraic-geometric statement independent of N, or identify the first extra smooth component; exact computations support rather than replace proof. |
| V-E5 | Robustness and limitations: compare function-level translation-preserving Hamming perturbations with unconstrained entrywise perturbations; separate pole budgets, approximation types, polynomial degree, rational representation, and actual arithmetic circuit cost. | Prove a quantitative restricted-model statement with explicitly charged features; include known rational addition and repeated-squaring controls. |
| V-E6 | Independent proof review and formalization of evaluation hyperplane, coordinate changes, residue identity, chart coverage, and matching-characteristic argument. | Reproducible receipts and reviewed proof; state any remaining axioms or premises. |

Use order-five exceptional cases and singular curves at orders 7-17 as positive controls, random even functions and arbitrary evaluation matrices as calibration controls, and multiple generators of the same subgroup as invariance checks. Record exact field models, point coordinates, pole value, generator, and results with canonical subgroup deduplication. Count distinct isomorphism classes separately from Weierstrass models, to avoid inflating evidence. All experiments stay on synthetic/toy data; no deployed keys or curves are needed.

## Important negative control: entrywise approximation

Let M be the symmetric matrix of the target on S x S and lambda the nonzero residue vector, with every coordinate nonzero. The lower-degree evaluation space is lambda^perp. Define a diagonal correction E_ii=-(M lambda)_i/lambda_i. Then (M+E)lambda=0 and M+E is symmetric, so it has a lower-degree decoder. At most |S| entries out of |S|^2 change. Thus the exact one-degree gap by itself cannot imply a large arbitrary-entry Hamming rigidity margin. Translation-preserving errors are a different model; any proposed stability theorem must distinguish them. This is a written linear-algebra argument, not a measured cryptographic result.

## Decision rule

Prioritize proof-oriented inexpensive experiments E1-E4. If the uniform conjecture fails, classify the smooth exceptional locus and publish the restricted result. If it survives, pursue a proof using the residue identity, local geometry, and modular-curve divisor theory rather than unlimited order-by-order enumeration. Advance claims beyond interpolation only after a precise theorem connecting the charged resources to a separately stated computational model, with known counterexamples addressed. The current results neither establish such a reduction nor support inferences about secret algorithms or model safety classifiers. No large compute spend is justified by this evidence alone.
