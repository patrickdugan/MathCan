# OLM-09: Endpoint observability and certified finite-radius causal ordering

**November 15, 2026.** Pure-math companion to [SMC-09](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc09-endpoint-interval-20261115/research/real_recurrence_sae_v1). Motivating results: OLM-07 causal Gram geometry, OLM-08 recurrent Hessian bounds, and the source-locked SMC-07/08 SAE measurements on a pretrained 44K Sudoku network.

**Status and mathematical priority.** The inequalities below follow from standard interval arithmetic, elementary topology and the Lipschitz inequality. The contribution is an auditable certificate contract for comparing *finite causal interventions on a fixed pretrained recurrent model*. No priority over preexisting interval-verification literature is claimed. Neither the broad OpenAI Math #131 and #238 papers nor a Lean proof supply these bounds.

## 1. A finite endpoint test, independent of curvature envelopes

Let \(F:\mathbb R^d\to\mathbb R^q\) be a fixed mathematical model, \(h\in\mathbb R^d\) a frozen input, \(r>0\) a fixed intervention radius, and \(u,v\) two exact unit vectors. Define the **finite causal displacement**

\[
\Delta_u(r)=F(h+ru)-F(h),\qquad
S_u(r)=\|\Delta_u(r)\|_2^2.
\]

Suppose a validated interval evaluator returns enclosures
\(B_{0j}\ni F_j(h)\), \(B_{uj}\ni F_j(h+ru)\), and \(B_{vj}\ni F_j(h+rv)\) for each \(j=1,\ldots,q\). Denote their interval differences \(D_{uj}=B_{uj}-B_{0j}\) and \(D_{vj}=B_{vj}-B_{0j}\). Use an inclusion isotonic interval square \({\rm sq}([a,b])\supseteq\{x^2:x\in[a,b]\}\) and calculate

\[
I_u=\sum_{j=1}^q {\rm sq}(D_{uj}),\qquad
I_v=\sum_{j=1}^q {\rm sq}(D_{vj}).
\]

**Theorem OLM-09A (finite endpoint dominance).** If

\[
\boxed{\inf(I_u)>\sup(I_v)}
\tag{1}
\]

then the exact-real finite-radius intervention along \(u\) has *strictly greater* output norm than the one along \(v\):

\[
\boxed{\|\Delta_u(r)\|_2>\|\Delta_v(r)\|_2.}
\tag{2}
\]

If the intervals overlap, the algorithm must mark this test inconclusive. Reversing the inequality certifies the reverse ordering.

**Proof.** Validated inclusion gives \(F_j(h+ru)-F_j(h)\in D_{uj}\) and hence its square belongs to \({\rm sq}(D_{uj})\). Add the \(q\) componentwise bounds to obtain \(S_u(r)\in I_u\); similarly \(S_v(r)\in I_v\). Strict separation yields \(S_u>S_v\ge0\), and the square root is strictly monotone on nonnegative reals. QED.

The certificate requires **only validated endpoint evaluations**. It does not assert a bound on \(D^2F\) over the entire segment, and therefore can resolve finite-radius comparisons even where the global OLM-08 Hessian bound is \(10^{53}\) or local Taylor transport becomes too broad. This is a finite-input result about the exact mathematical function at the exact specified endpoints; it says nothing about all nearby directions or amplitudes.

## 2. Equal-radius directions defined by exact source binaries

A trained SAE and a numerical Jacobian may supply FP64 direction vectors. Interpret the 48 stored FP64 components of a nonzero direction \(v\) as **exact dyadic rationals** \(v_j\in\mathbb Q\). Define the exact-real unit direction

\[
u_j=\frac{v_j}{\sqrt{\sum_\ell v_\ell^2}}.
\]

**Lemma OLM-09B (precision-independent radius contract).** The exact mathematical \(u\) has \(\|u\|_2=1\), and thus \(h+ru\) has Euclidean distance \(r\) from \(h\), for every positive rational \(r\). A validated interval evaluation of the normalization followed by the recurrence encloses the exact-real endpoint \(h+ru\). Direction selection can be numerical, while the **chosen direction and the evaluated endpoint** are fixed by this exact binary-to-real specification.

**Proof.** The denominator is strictly positive. Its square is the exact sum of the coordinate squares; division yields \(\sum u_j^2=1\). Composing valid interval inclusions of positive square root, division, addition and the smooth recurrence preserves enclosure. QED.

This separates the heuristic search for a feature direction from a rigorous verification of the *selected* direction. It does not certify that an FP64 autograd eigenvector is the true dominant right singular vector of the exact-real Jacobian.

## 3. Stability under direction and anchor uncertainty

Endpoint certificates can also support a robustness statement **if** an independent Lipschitz bound is available. Suppose \(F\) is \(L\)-Lipschitz on a domain containing every relevant input and intervention endpoint. Let a nominal direction \(u\) be replaced by \(u'\) with \(\|u-u'\|\le\delta_u\), and nominal anchor \(h\) by \(h'\) with \(\|h-h'\|\le\delta_h\). By applying the triangle inequality to the two terms of the displacement,

\[
\big|\|F(h'+ru')-F(h')\|-
       \|F(h+ru)-F(h)\|\big|
\le L(r\delta_u+2\delta_h).
\tag{3}
\]

**Theorem OLM-09C (robust finite-radius dominance).** If the interval endpoint calculations give a nominal lower effect bound \(\ell_u=\sqrt{\max(0,\inf I_u)}\) and upper effect bound \(b_v=\sqrt{\max(0,\sup I_v)}\), then

\[
\boxed{\ell_u-b_v >
L\big(r(\delta_u+\delta_v)+4\delta_h\big)}
\tag{4}
\]

is sufficient to certify strict dominance for *all* admissible perturbed anchors and directions obeying these error budgets.

**Proof.** Take the difference of the two nominal output norms and apply (3) once to each intervention. For the same uncertain anchor \(h'\), each perturbation incurs at most \(L(r\delta+2\delta_h)\); subtract both worst-case errors to obtain (4). QED.

The existing exact-real global Lipschitz envelope is extremely conservative, so this robustness certificate might be uninformative. A finite endpoint certificate at one frozen input remains valid without applying (4).

## 4. Gauge and dictionary reindexing

Let an SAE dictionary be \(D\in\mathbb R^{d\times m}\), and let \(P\) permute its feature indices. Set \(D'=DP\) and \(z'=P^\top z\). Then \(D'z'=Dz\); any physically identical intervention direction gives identical \(F(h+ru)\), and therefore identical \(I_u\) up to enclosure precision. When feature selection uses the **unique** maximum nonnegative activation, the selected atom transforms consistently under this permutation.

This is a feature-index gauge invariance of physical intervention outcomes. An arbitrary dense invertible change of latent coordinates need not preserve top-k sparsity or the selected-atom rule.

## 5. Scientific application and exactness boundaries

SMC-08 measured numerically that the active learned SAE decoder atom yielded larger equal-radius final goal-logit effects than seeded isotropic directions in 15/16 heldout puzzles, while the Jacobian-maximal direction exceeded the SAE atom on all 16. The analysis used the same previously inspected 16-puzzle roster as SMC-07, so its outcomes are explanatory and not fresh confirmatory evidence. Its Arb local Taylor bounds certified the sign of a scalar winner-versus-runner margin at very small radii, up to approximately \(1.23\times10^{-8}\).

SMC-09 changes the *proof target* to the exact ten-logit L2 causal effect at frozen radius 0.02, 0.2 and 0.8. It uses source-locked weights, exact binary stage-one anchors, exact-rational intervention radii and the normalized dyadic direction definition above. The inherited Arb forward engine encloses the complete recurrent computation, including erf-GELU and LayerNorm, using outward rounding. A distinct output label now signifies strict endpoint effect ordering.

No claim about FP64 Torch kernel roundoff, correctness on other datasets, sensitivity for an entire open radius range, or causal feature semantics follows solely from these finite comparisons. The mathematical novelty resides in the experimental synthesis and auditable separation of certified fixed-endpoint results from uniform-tube questions; the abstract inequalities themselves are standard.

## Verification

The [exact rational oracle](endpoint_ordering.py) and [regression tests](../../tests/test_endpoint_ordering.py) check interval inclusion, strict separation, ties and a robust Lipschitz uncertainty margin without neural model dependencies. The [SMC-09 implementation](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc09-endpoint-interval-20261115/research/real_recurrence_sae_v1/smc09_endpoint_arb.py) provides the source-locked numerical-selection/validated-evaluation interface, with hosted pilot/full jobs and their separate receipts.
