# DEL-08: fixed-coefficient hyperplane and geometric Bertini audit

Date: 2026-11-22. Source: [Hexagon 2611.00789v1](https://hexagonmath.org/2611.00789v1), **Lemma 8** and Theorem 9 (PDF pages 6–8). Geometric input: N. Katz, *Affine cohomological transforms, perversity, and monodromy* (JAMS 1993), Appendix A.3–A.5, pp. 219–221, [author PDF](https://web.math.princeton.edu/~nmk/old/ACT.pdf).

The Hexagon exposition identifies itself as AI-authored and unverified by a human. DEL-08 is an independent check of the geometric parameter construction. It is a conditional formalization of several algebraic steps, not a verification of the entire weak Lefschetz theorem.

## 1. The exact fixed-coefficient argument

Let (V) be a smooth affine variety of pure dimension (D\ge1). Suppose (y_1,\ldots,y_M) are functions inducing a closed immersion (\Gamma:V\to\mathbb A^M). Katz's Theorem A.5 applies to the composite map into (\mathbb P^M), which is **quasi-finite**. For a lisse sheaf (\mathcal G), the shift (\mathcal G[D]) is perverse. Hence there is a dense Zariski open (L) of hyperplanes for which the ordinary restriction is an isomorphism for (a<D-1), and injective for (a=D-1).

A separate geometric Bertini argument provides a dense open (S) of hyperplanes whose inverse images are smooth, pure dimension (D-1), or empty on each connected component. For an immersion, the bad tangency incidence space has dimension at most (D+(M-D-1)=M-1) when (M>D). For (M=D), the tangent hyperplane fiber is empty. Properness of the hyperplane incidence projection (or taking the closure of its constructible image) gives a proper bad closed locus in the (M)-dimensional hyperplane space.

In the standard affine hyperplane chart, write an equation

[
\sum_{i=1}^{M-1} a_i y_i + \lambda y_M+c=0.
]

The locus (C=\{\lambda\ne0\}) is a nonempty open subset of the projective hyperplane parameter space. Since (S\cap L) is dense open, it meets (C). Dividing by (\lambda) gives

[
y_M+\sum_i (a_i/\lambda)y_i+c/\lambda=0.
]

The coefficient of the designated last coordinate is **exactly 1**, as required by the Fourier phase. The division changes neither the zero subscheme nor smoothness.

The Lean theorem `good_hyperplane_in_fixed_chart` proves the topological intersection given the two dense opens and the nonempty open chart. `hyperplane_normalization` and `hyperplane_zero_iff_fixed` prove the algebraic rescaling over any field. The genuinely geometric construction of (S) and (L), their Zariski topology, and the identification of the chart with projective hyperplanes remain separate hypotheses.

## 2. The graph of the prescribed bilinear function

For Theorem 9, choose an affine closed immersion (z:U\to\mathbb A^s), extend it componentwise to (z^k:U^k\to\mathbb A^{sk}), and define the fixed regular function

[
B(u_1,\ldots,u_k)=\sum_{j=1}^{k-1}b(\pi(u_j),\pi(u_{j+1})).
]

The map (Gamma=(z^k,B):U^k\to\mathbb A^{sk+1}) is a **graph of a regular function** over an existing closed immersion. The first (sk) coordinates already separate and algebraically generate the coordinate ring.

More precisely, if (f:A\twoheadrightarrow C) is a surjective coordinate-ring homomorphism and (B\in C), the evaluation homomorphism (A[T]\to C) taking (T\mapsto B) is surjective because every (c\in C) is the image of a constant polynomial (f(a)). Mathlib proves that surjective morphisms of affine coordinate rings induce closed immersions of affine schemes. DEL-08 formally proves **both** the ring-surjectivity step and its actual affine-scheme closed immersion conclusion. The product closed immersion (z^k) is a standard geometric premise not yet formalized in MathCan.

If the original coordinates fail to embed, graphing an extra function can lose points: ((x,y)\mapsto(x,xy)) identifies ((0,0)) with ((0,1)) over every tested finite field. This mutation prevents replacing the closed-immersion hypothesis by an arbitrary morphism.

## 3. Tangency and characteristic-free smoothness

The incidence dimension count is valid for a closed immersion in arbitrary characteristic. DEL-08 kernel-checks its integer inequality, while the scheme-theoretic tangent-space/semicontinuity argument remains in the geometric premise.

There is also a useful **constructive special case**. Any bipartite quadratic
[
Q(x,y)=\sum_i x_i\sum_j A_{ij}y_j
]
satisfies
[
Q(x,y)=\sum_i x_i\frac{\partial Q}{\partial x_i}.
]
This identity is valid in characteristic 2, with no division by 2. If (c\ne0), every point on (Q+c=0) has a nonzero (x)-partial derivative; otherwise the equation would imply (c=0). Thus the hypersurface is geometrically smooth (or empty) by the affine Jacobian criterion.

The path phase (sum_j x_jx_{j+1}) is bipartite under its even/odd vertex partition. Hence, on **unconstrained affine space**, taking its constant term (c=1) gives an explicit smooth hypersurface in every characteristic. `bipartite_euler_identity` and `bipartite_nonzero_level_regular` formalize the algebraic gradient certificate.

This special case must not be imported as a smoothness proof on general (U^k). Even when an ambient hypersurface is smooth, its restriction to a smooth embedded subvariety can be singular. A concrete mutation takes (xy+1=0) in (\mathbb A^2), which is smooth, and the smooth tangent line (y=x-2). Restriction gives ((x-1)^2=0), a nonreduced singular section. DEL-08 tests this over characteristics 2, 3 and 5 and their small extensions. The actual Bertini open on the embedded (U^k) remains essential.

For the family (xy+ax+by+c=0), simultaneous vanishing of its two partial derivatives occurs precisely at (x=-b,y=-a); this point belongs to the hypersurface exactly when (c=ab). Thus ({c\ne ab}) is a concrete nonempty Zariski open of smooth fixed-coefficient sections. The full criterion is a Lean theorem, and its finite-field counts have (q^2(q-1)) good versus (q^2) singular parameters.

## 4. Rationality over some finite extension

A nonempty Zariski open of an affine parameter space over (\overline{\mathbb F}_q) has a geometric point; the finitely many coordinates of that point belong to a common **finite extension** (\mathbb F_{q^e}). The extension degree (e) can depend on (k), which is permitted by DEL-05.

The extension can be necessary. Over (\mathbb F_p), every rational (x) satisfies (x^p-x=0). The principal open (D(x^p-x)) is nonempty and dense as a scheme but has **no (\mathbb F_p)-rational points**. Over (\mathbb F_{p^2}), it has (p^2-p) points. DEL-08 checks this exactly for ((p,q^2)=(2,4),(3,9),(5,25)).

This is an executable warning against requiring the fixed-coefficient hyperplane already over the base field. A generic-open argument cannot guarantee an (\mathbb F_q)-rational parameter. MathCan has not yet formalized the general fact that geometric points of a finite-type parameter scheme over (\overline{\mathbb F}_q) descend to some finite extension.

## 5. Evidence and acceptance

The branch contains two Mathlib modules under `experiments/deligne_mathlib/Deligne04/`:

- `FixedCoefficientChart.lean`: closed immersion of the graph, exact coefficient normalization, dense-good-open chart intersection, and incidence dimension arithmetic.
- `BipartiteSmoothness.lean`: characteristic-free Euler/gradient certificate and the exact conic discriminant.

The standard-library Python oracle `del08_oracle.py`, unittest module and 80-case JSONL verifier check finite extensions, zero-last-coefficient failures, singular discriminants, ambient tangent restrictions, and nonembedding coordinates.

**Formal boundary:** The general geometric Bertini smoothness theorem and Katz weak Lefschetz remain premises. The proof of Lemma 8 as a complete theorem about actual schemes and perverse sheaves still needs a formalization of quasi-finite projective embeddings, tangent incidence dimension, constructible sheaves and generic base change.

Required gates: pinned Mathlib 4.35 kernel with no `sorryAx`, exact Python tests, MathCan-wide CI. The complete proposed Deligne proof still requires independent review by a human expert in étale cohomology.
