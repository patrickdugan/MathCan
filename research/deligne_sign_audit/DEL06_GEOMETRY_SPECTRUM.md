# DEL-06: Gysin sign and tensor Frobenius bridge

**Source:** [Hexagon 2611.00789v1](https://hexagonmath.org/pdf/2611.00789v1),
Section 5, Proposition 4, pp. 5–6; Theorem 7 and Lemma 8, pp. 6–7.
**Date:** 2026-11-22.
**Target repository:** patrickdugan/MathCan, isolated Lean/Mathlib 4.35 project.
**Upstream:** DEL-01 sign audit, DEL-02 Fourier oracle, DEL-03 Hankel poles,
DEL-04 all-positive-powers theorem, DEL-05 tensor-extension limit.

## Source identity and proof boundary

Let \(U\) be smooth affine of pure dimension \(d\ge1\), with a
lisse \(\ell\)-adic sheaf \(\mathcal F\). Put \(X=U^k\) and
\(D=kd\). A smooth hypersurface \(Y\subset X\), including a possibly
empty section, must have the weak Lefschetz restriction property in
cohomological degrees \(a<D-1\) and \(a=D-1\).

Poincaré duality converts that property into Frobenius-equivariant Gysin
maps

\[
G_a:H_c^{D-1+a}(Y,\mathcal F_k)(-1)
  \longrightarrow H_c^{D+1+a}(X,\mathcal F_k).
\]

The map is an isomorphism for \(a\ge1\) and surjective for \(a=0\).
Its border kernel \(K=\ker G_0\) is an actual Frobenius module. The
fixed source gives, for every \(n\ge1\),

\[
R_n=r^nN_n-M_n^k,\qquad
(-1)^{D-1}R_n=
\operatorname{Tr}(F^n\mid H_c^d(U,\mathcal F)^{\otimes k})
+\operatorname{Tr}(F^n\mid K).
\]

**The geometric existence of these maps and all étale-cohomological
comparison theorems remain outside DEL-06.** The mathematical proof
posted to Hexagon is AI-generated and has received no reported human
verification as of 2026-11-22. A kernel certificate here concerns only
the statements explicitly represented in Lean.

## 1. Genuine kernel and quotient traces

Choose an algebraic basis adapted to a Frobenius-stable kernel and its
surjective Gysin quotient. The Frobenius matrix is

\[
B=\begin{pmatrix}F_K & E\\0&F_Q\end{pmatrix}.
\]

The cross-block \(E\) may be arbitrary. In every power \(n\),

\[
B^n=\begin{pmatrix}F_K^n&E_n\\0&F_Q^n\end{pmatrix},
\qquad
\operatorname{Tr}(B^n)=
\operatorname{Tr}(F_K^n)+\operatorname{Tr}(F_Q^n).
\]

The Lean files GysinTrace.lean and GysinPowers.lean establish the
matrix-level identities, including an actual arbitrary upper-right
block. Their hypotheses correspond to the existence of a
Frobenius-stable kernel and a quotient basis. This does not assume that
the original Frobenius matrix is diagonalizable.

## 2. Cancellation above the boundary

An equivariant Gysin isomorphism between two high-degree modules
becomes, in bases, a conjugacy

\[
F_Y=P F_X P^{-1}.
\]

Therefore for every \(n\ge0\),

\[
\operatorname{Tr}(F_Y^n)=\operatorname{Tr}(F_X^n).
\]

The source combines the two trace formulas using the sign
\((-1)^{D-1}\). Each higher Y degree cancels the corresponding X
degree with opposite parity, leaving

\[
\operatorname{Tr}(B^n)-\operatorname{Tr}(F_Q^n)
+\operatorname{Tr}(F_L^n)
=\operatorname{Tr}(F_K^n)+\operatorname{Tr}(F_L^n),
\]

where \(L\) is the lowest cohomology of \(X\).

The formal theorem proposition4_all_positive_powers records the
remaining trace-formula premise explicitly. The algebraic cancellation
itself is kernel-checked.

The current higher-degree matrix interface gives high pairs a common
finite dimension, as an implementation convenience. The source permits
dimensions to vary with cohomological degree. A future generalized
sigma-indexed interface should remove that convenience without
changing the argument.

## 3. Tensor eigenvalues, including nonsemisimple Frobenius

The pure finite tensor spectral model uses indices
\(x:\mathrm{Fin}\,k\to\mathrm{Fin}\,n\), with

\[
\lambda_x=\prod_{i=1}^k\lambda_{x(i)}.
\]

For any eigenvalue \(\alpha=\lambda_j\), the constant index \(x(i)=j\)
produces \(\alpha^k\), and

\[
\sum_x\lambda_x^e=
\left(\sum_j\lambda_j^e\right)^k.
\]

TensorSpectrum.lean proves these statements for a diagonal spectral
model.

The stronger MatrixTensorEigen.lean models an **arbitrary** complex
matrix \(A\) by the k-fold tensor operator

\[
T_k(A)_{x,y}=\prod_{i=1}^k A_{x(i),y(i)}.
\]

If \(Av=\alpha v\) with a nonzero coordinate of \(v\), the constructed
tensor \(w_x=\prod_i v_{x(i)}\) is nonzero and satisfies

\[
T_k(A^e)w=\alpha^{ke}w.
\]

Thus the tensor occurrence calculation works for matrices with
nontrivial Jordan blocks. As in Lemma 2, semisimplicity of Frobenius
is not an assumption. Passing from the actual \(\mathbb Q_\ell\)
cohomology to this complex matrix realization, together with the
Künneth map, remains a separate interface.

## 4. Tate twist and source sign

On Frobenius eigenvalues, the twist \((-1)\) contributes a scalar
factor \(r\), so its n-th power contributes \(r^n\). Missing the
exponent n changes the point-count remainder.

The signed remainder uses \((-1)^{D-1}\) and the base field size
\(r\) of the hypersurface's field of definition. It should be kept
distinct from the original \(q\) when a suitable generic
hypersurface exists only over \(\mathbb F_{q^e}\).

The matrix trace-sign theorems explicitly exhibit the kernel's
positive contribution. They do not prove the existence of a
geometrically suitable hyperplane section.

## 5. Exact finite regression and mutation examples

The Python verifier geometry_trace.py uses fractions.Fraction for
all matrix operations, Frobenius powers, tensor traces and Tate
factors. Tests include nonsplit upper-triangular extensions and
nondiagonal high-degree Frobenius matrices. They check the full
all-powers identities and source sign.

The 72-case corpus del06_tasks.jsonl covers:

- 20 valid boundary kernel/quotient trace decompositions.
- 10 lower-left block mutations, which break kernel stability and
  fail from the second Frobenius power onward.
- 10 Tate-twist examples that distinguish \(r^n\) from \(r\).
- 12 tensor-spectrum power-sum and eigenvalue occurrence cases.
- 6 Künneth vanishing mutants that admit mixed cohomological degrees.
- 6 signed virtual-cancellation mutants.
- 8 signed-point-remainder parity cases.

Each case is checked by verify_del06_tasks.py and has an exact,
deterministic label. Passing these small models does not assert a
general geometric theorem.

## 6. Remaining geometric work

The formal mathematical gaps, in the order they matter to the source,
are:

1. **Construct the actual l-adic cohomology and its Frobenius action.**
   Provide duality and the compactly supported trace formula.
2. **Connect the actual Gysin map to its kernel-stable matrix model.**
   The geometric input requires the precise shifted degree maps,
   surjectivity at D-1, and isomorphisms above it.
3. **Prove the actual Künneth tensor identification and
   eigenvalue extension**, respecting the fixed embedding
   \(\iota:\overline{\mathbb Q}_\ell\hookrightarrow\mathbb C\).
4. **Construct the generic hypersurface of Lemma 8** with fixed
   bilinear coefficient and the exact weak Lefschetz hypotheses of
   Katz A.5. This is the principal geometric result still outside the
   formal project.
5. **Connect the all-powers point-count remainder to DEL-02's Fourier
   estimate**, including the finite map to affine space and the local
   trace-weight bounds.

A reviewer should inspect the paper's geometric dependencies
independently, particularly the fixed-coefficient hyperplane choice.
The formally proved algebraic statements are reusable even if that
geometric argument changes.
