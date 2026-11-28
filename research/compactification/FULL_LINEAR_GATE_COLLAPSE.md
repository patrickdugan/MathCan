# NRF-05: full-support gate collapse and a uniform leakage gap

**Date:** November 15, 2026. **Status:** research-program theorem, written proof, exact-rational regression tests, and independently recomputable finite-field witnesses from the existing twelve trained checkpoints. Mathematical priority has not been established. The matrix-invariant-subspace ideas connect to classical Kalman observability and exact nonlinear lumpability.

## Model and quantified claim

Let \(W_1,W_2\in\mathbb R^{n\times n}\), \(b_1,b_2\in\mathbb R^n\), and \(\beta\ne0\). Consider the **full-domain**, smooth tied update

\[
F(x)=\alpha x+\beta W_2\tanh(W_1x+b_1)+\beta b_2,\qquad x\in\mathbb R^n.
\]

Write \(a_j=W_2e_j\), \(b_j^{\rm row}=W_1^Te_j\), and \(H=W_1W_2\). Suppose

1. \(W_1\) is invertible;
2. \(W_2\) is invertible;
3. every entry \(H_{jk}\) is nonzero.

**Theorem NRF-05A (full-linear-observation no-go).** For any real linear observation \(C:\mathbb R^n\to\mathbb R^r\) of rank \(0<k<n\), there exists no deterministic map \(f\) on its image satisfying

\[
CF(x)=f(Cx)\quad\text{for all }x\in\mathbb R^n.
\]

This applies to *every* nonzero rank-eight linear decoder, including target-supervised decoder directions, under the stated global hypotheses. It does not concern nonlinear decoders or observations restricted to a reachable subset.

**Proof.** If \(F\) factors through \(C\), its derivative preserves the observation fibers. Equivalently, for \(S=\operatorname{row}(C)\), \(SJ_F(x)\subseteq S\) for every \(x\), where

\[
J_F(x)=\alpha I+\beta W_2D(x)W_1,\qquad
D(x)=\operatorname{diag}(\operatorname{sech}^2(W_1x+b_1)).
\]

Because \(W_1\) is invertible and the domain is all \(\mathbb R^n\), the entries of \(D(x)\) can independently take arbitrary values in \((0,1]\). Linearity and differences of such diagonals imply \(S(W_2E_jW_1)\subseteq S\) for every \(j\).

Choose a nonzero row \(s\in S\). Invertibility of \(W_2\) gives \(sW_2\ne0\), so for some index \(j\), \(s a_j\ne0\). Rank-one invariance then forces \(b_j^{\rm row}\in S\). Since \(H_{j\ell}= (b_j^{\rm row})^Ta_\ell\ne0\) for every \(\ell\), invariance forces **every** row \(b_\ell^{\rm row}\) into \(S\). Invertibility of \(W_1\) means these rows span \(\mathbb R^n\), and \(S=\mathbb R^n\), contradicting \(k<n\). \(\square\)

The proof also shows that the independent-gate closure of **any** nonzero rowspace reaches all \(n\) dimensions after at most two rounds of rank-one gate propagation.

## Theorem NRF-05B: strictly positive global leakage floor

For an orthogonal projector \(P\) of rank \(1\le k<n\), put

\[
\Lambda(P)=\max_j
\|P a_j\|_2\,\|(I-P)b_j^{\rm row}\|_2.
\]

Let \(\sigma_1=\sigma_{\min}(W_1)\), \(\sigma_2=\sigma_{\min}(W_2)\), \(A=\max_j\|a_j\|_2\), \(B=\max_j\|b_j^{\rm row}\|_2\), and \(h=\min_{j,\ell}|H_{j\ell}|>0\). Then

\[
\boxed{\Lambda(P)\ \ge\
\frac{h}{2\sqrt n}
\min\left(\frac{\sigma_2}{A},\frac{\sigma_1}{B}\right)>0.}
\]

**Proof.** Since \(\sum_j\|Pa_j\|_2^2=\|PW_2\|_F^2\ge k\sigma_2^2\), some \(j\) has \(\|Pa_j\|\ge\sigma_2/\sqrt n\). Let \(\delta=\Lambda(P)\). Consequently \(\|(I-P)b_j^{\rm row}\|\le\delta\sqrt n/\sigma_2\).

If \(\delta<h\sigma_2/(2A\sqrt n)\), then for every \(\ell\)

\[
h\le |\langle b_j^{\rm row},a_\ell\rangle|
\le B\|Pa_\ell\|+(\delta\sqrt n/\sigma_2)A,
\]

so \(\|Pa_\ell\|\ge h/(2B)\). Definition of \(\delta\) now gives \(\|(I-P)b_\ell^{\rm row}\|\le 2B\delta/h\) for every \(\ell\). Yet

\[
\sum_\ell\|(I-P)b_\ell^{\rm row}\|^2
=\|(I-P)W_1^T\|_F^2\ge(n-k)\sigma_1^2,
\]

so at least one \(\ell\) satisfies \(\|(I-P)b_\ell^{\rm row}\|\ge\sigma_1/\sqrt n\). Thus \(\delta\ge h\sigma_1/(2B\sqrt n)\). In the complementary case the first bound already applies. This establishes the displayed uniform lower bound.

Moreover the global state space lets \(D(x)\) approach any gate \(E_j\), so

\[
\sup_{x\in\mathbb R^n}\|P J_F(x)(I-P)\|_2
\ge|\beta|\Lambda(P).
\]

The nonlinear map therefore has a strictly positive **global** dark-to-observed differential leakage floor in every proper linear observation subspace. These bounds can be extremely small and do not imply a measurable effect on a bounded or data-supported subset.

## Exact binary32 finite-field certificate

For every finite IEEE-754 binary32 value, \(2^{149}w\in\mathbb Z\). Given a prime \(p\), reduction of the exact integer \(2^{149}w\) modulo \(p\) preserves a one-way rank witness: if the matrix is nonsingular modulo \(p\), it is nonsingular over \(\mathbb Q\) and \(\mathbb R\). The scaled product \((2^{149}W_1)(2^{149}W_2)=2^{298}H\) has integer entries. If a particular entry is nonzero modulo \(p\), the corresponding real entry of \(H\) is **exactly nonzero**.

NRF-05 analyzed the 12 existing SHA-256-pinned tied ToyLoop checkpoints from MoralityLabAI/LoopedTransformers, depths 16/32, seeds 101/103/107, state-visit exposures 2048/4096. At \(p=67,108,859\), the modular ranks of both \(W_1\) and \(W_2\) are 128 in every checkpoint; all \(128^2=16,384\) entries of \(2^{298}W_1W_2\) reduce to nonzero residues. An independent check of \(W_2\) at \(p=65,521\) also produces nonzero determinants in all twelve. The checkpoint SHA-256 values had been verified against original frozen experiment events in NRF-03.

The private applied repository retains the exact determinant residues and expected matrix-product nonzero counts alongside a PyTorch checkpoint verifier. The public MathCan tests exercise the corresponding theorem hypotheses with small exact rational matrices and enumerate all 148 nonzero integer observation directions in two and three dimensions.

The earlier NRF-04 coordinate-only closure was a weaker claim. **This result establishes the global obstruction for every nonzero linear observation subspace**, not merely coordinate projections. It leaves finite-horizon, restricted-state and distribution-specific approximate quotient design as the meaningful next direction.

## Formalization and boundary

\`MathCan/GateFamilyNoGo.lean\` proves the graph-support saturation step at the level of predicates; the matrix-invertibility, tanh derivative argument, and quantitative singular-value bound above remain written proofs. The exact rational finite tests are in \`research/compactification/global_gate_nogo.py\` and \`tests/test_global_gate_nogo.py\`. The native binary32 matrix calculation is independently verifiable from the private frozen checkpoint files.

The selected source pair remains OpenAI's September 2026 complete Crouzeix-inequality and reflexive-space fixed-point preprints. NRF-05 is a downstream obstruction derived from the trained tanh residual dynamics, using the same research questions. Its proof is independent of either preprint's unverified general claims.
