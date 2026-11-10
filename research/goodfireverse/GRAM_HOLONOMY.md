# GFR-01: Pairwise projector data, loop holonomy, and a triple invariant

**Status:** Exact linear algebra and finite rational examples (2026-11-10). The geometry is independent of the training status of any neural network.

**Motivation:** [Goodfireverse's research index](https://github.com/patrickdugan/Goodfireverse/blob/b3f8e2932e5b18af591d4970b16ce7ceb4472e63/reports/coverage.md) includes research on neural geometry, manifolds, and feature decompositions. [RSITopology](https://github.com/MoralityLabAI/RSITopology/blob/4f6f93da08202bc1b81d24d371fe11826d352e4a/reports/monitor_holonomy_insight.md) studies path-dependent transport of signed coordinates across context and checkpoint loops. This note gives a minimal exact witness distinguishing *pairwise scalar overlap summaries* from a gauge-invariant loop quantity. The claims are MathCan's mathematical formulation and do not attribute an unverified theorem to Goodfire.

## 1. Rank-one observation data

Let `u₀,u₁,u₂` be unit vectors in a real Euclidean space and `P_i=u_i u_iᵀ` the orthogonal projector onto the line of `u_i`. Set `g_ij = ⟨u_i,u_j⟩` and suppose the three pairwise overlaps are nonzero. A common pairwise geometric statistic is

\[
\operatorname{tr}(P_iP_j)=g_{ij}^2,\qquad
\|P_i-P_j\|_F^2=2(1-g_{ij}^2).
\]

For rank-one real frames the orthogonal factor of the overlap is simply `sign(g_ij)`. Its triangle holonomy is

\[
H_{012}=\operatorname{sign}(g_{01}g_{12}g_{20})\in\{-1,+1\}.
\]

This is the real rank-one form of a Bargmann/Pancharatnam cycle sign. The construction below is a finite-dimensional example of that established geometric idea.

## 2. Identical pairwise scalar data with opposite loop signs

Take `a=1/4` and the two symmetric Gram matrices

\[
G_+=\begin{pmatrix}1&a&a\\a&1&a\\a&a&1\end{pmatrix},\quad
G_-=\begin{pmatrix}1&a&-a\\a&1&a\\-a&a&1\end{pmatrix}.
\]

**GFR-01/T1 (realizability).** Both matrices are Gram matrices of triples of unit vectors in `R³`.

*Proof.* Their leading principal minors are `1`, `1-a²=15/16`, and `det(G_+)=27/32`, `det(G_-)=25/32`. Sylvester's criterion makes both positive definite. Every real positive-definite matrix admits a Gram factorization; diagonal entries one ensure the corresponding vectors have unit length.

**GFR-01/T2 (pairwise data no-go).** Every off-diagonal squared Gram entry equals `1/16` in both triples, so their three pairwise projector overlaps and all three Frobenius projector distances agree. Nevertheless,

\[
H_{012}(G_+)=+1,\quad H_{012}(G_-)=-1.
\]

*Proof.* The products `g₀₁g₁₂g₂₀` are respectively `+a³=1/64` and `-a³=-1/64`. All individual squared overlaps equal `a²`.

The precise information loss is in retaining **only pairwise overlap magnitudes or principal angles**. A full set of projectors as matrices contains an additional triple invariant; the example is not a no-go for full projector observations.

## 3. The missing observable and gauge invariance

**GFR-01/T3 (triple-projector invariant).**

\[
\operatorname{tr}(P_0P_1P_2)=g_{01}g_{12}g_{20}.
\]

*Proof.* Multiply the rank-one matrices: `P₀P₁P₂ = u₀ (u₀ᵀu₁)(u₁ᵀu₂) u₂ᵀ`; take the trace using `tr(u₀u₂ᵀ)=u₂ᵀu₀`. Hence its sign recovers the loop sign whenever none of the three overlaps is zero. For `G_+` and `G_-`, it equals `+1/64` and `-1/64`.

**GFR-01/T4 (invariance under local frames).** Replacing the unit representative `u_i` by `σ_i u_i`, `σ_i∈{−1,+1}`, leaves `P_i`, the pairwise squared overlaps, the triple trace, and `H₀₁₂` unchanged.

*Proof.* The transformation sends `g_ij→σ_iσ_jg_ij`. Each `σ_i` appears twice in the triple product, so the combined factor is one; squares are also unchanged.

The triangle sign is thus invariant under independent frame choices while pairwise scalar measurements cannot determine it. Any use as a model-identity diagnostic must measure a compatible triple or transported loop and specify the reference space.

## 4. Higher rank: conjugacy of orthogonal holonomy

Let orthonormal column frames `U_i` of rank `r` have invertible overlaps `G_ij=U_iᵀU_j`. Let `R_ij` be the orthogonal polar factor of each `G_ij`, and let `H=R_01 R_12 ⋯ R_(k-1)0` around a closed loop. For a change of local bases `U_i→U_i Q_i` with orthogonal `Q_i`,

\[
R_{ij}\longmapsto Q_i^\top R_{ij}Q_j,\qquad
H\longmapsto Q_0^\top HQ_0.
\]

**GFR-01/T5 (holonomy conjugacy).** The conjugacy class and characteristic polynomial of `H` are independent of the chosen local orthonormal bases.

*Proof.* Left/right orthogonal multiplication preserves the polar decomposition of an invertible matrix and transports its unique orthogonal factor as shown. Multiplying factors around the loop cancels all intermediate basis rotations, leaving conjugation at the starting node. Conjugation preserves characteristic polynomial and trace.

The proof assumes invertible overlaps, a common ambient inner product, and a fixed cyclic path. Singular overlaps require a separate partial-isometry convention; arbitrary site matching is not covered.

## 5. Reproducibility and research boundary

Run:

```sh
python -m unittest tests.test_goodfireverse -v
```

The suite verifies both positive-definite Gram witnesses with exact fractions, their identical pairwise data and opposite cycle signs, all eight sign gauges for each configuration, and an exact `2×2` orthogonal gauge-conjugacy identity. A proposed neural-network experiment should compare pairwise principal angles with triple traces or full polar-loop products while freezing the subspace estimator and transport convention. Neural evidence would require held-out runs and a separate measurement protocol.
