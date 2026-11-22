# DEL-02: prime-power Fourier certificates and a sharp odd-path family

**Status:** exact finite computational checks plus a mathematical recurrence.
**Source:** [Hexagon 2611.00789v1](https://hexagonmath.org/2611.00789v1),
Section 4, Lemma 3. This work extends MathCan DEL-01.
**Formal status:** the general Fourier theorem, spectral Lemma 2, and
etale-geometric bridge remain unformalized.

## A universally sharp odd-length family

Let E be *any* finite field, A=E^d with |A|=N=q^d, let psi be a
nontrivial additive character and h a nonzero field element.
For each i choose a nondegenerate E-bilinear form b_i on A.
Define the all-one-weight path sum

\[
S_k(c) = \sum_{x_1,\ldots,x_k\in A}
  \psi\left(h\left(c+\sum_{i=1}^{k-1}b_i(x_i,x_{i+1})\right)\right).
\]

For k >=3, summing over x_1 gives N when x_2=0, and zero otherwise,
because x_1 maps to b_1(x_1,x_2) as a nonzero linear functional
whenever x_2 differs from zero. The term b_2(0,x_3) vanishes, hence

\[
S_k(c) = N S_{k-2}(c).
\]

The bases are S_1(c)=N psi(hc) and S_2(c)=N psi(hc).
Consequently, **for every k >=1**

\[
\boxed{S_k(c)=\psi(hc)N^{\lceil k/2\rceil}}.
\]

In particular, for every odd k >=3,

\[
|S_k(c)|=q^{d(k+1)/2},
\]

**equality in Lemma 3 for T=1**. This shows its general exponent is
optimal for infinitely many k, including with nonconstant sequences of
nondegenerate forms. For even k the ratio to the Lemma 3 upper bound is
q^{-d/2}. This is a symbolic argument independent of computational
experiments, relying only on elementary finite-field character
orthogonality; it is a narrow proof about the character-sum lemma,
not Deligne's weight theorem.

## Exact computational implementation

The finite-field implementation covers F_2,F_3,F_4,F_5,F_8,F_9,
F_16,F_25,F_27, with irreducible moduli pinned in code. Each finite
extension is represented as a polynomial residue class. The absolute
trace Tr(F_{p^m}/F_p) defines the nontrivial character
psi(x)=zeta_p^{Tr(x)}.

For each nonzero row difference the oracle counts the p trace fibers,
requiring every fiber to have exactly q^d/p points. That is an exact
finite arithmetic certificate for K K* = q^d I.

Character sums use a transfer-matrix contraction over integer
cyclotomic coefficients. The independent direct path enumeration agrees
on small cases. The tests also check changing bilinear forms and
weights in Z[zeta_p]. For p=5 the squared magnitude is computed as

\[
|\sum_{j=0}^4 c_j\zeta_5^j|^2
=\frac{2\sum c_j^2-A-B+(A-B)\sqrt5}{2},
\]

where A sums products c_i c_j for separation 1 or 4 and B sums those
for separation 2 or 3. Comparisons with integer bounds use only
integer squares and sign checks; there is no floating-point tolerance.
The p=2,3 cases have integer squared norms.

The path estimate checked is

\[
|S_k|^2 \le T^{2k}q^{d(k+1)},
\]

where T is an explicitly validated integer upper bound for the
cyclotomic-valued local weights.

## Controls and acceptance

- Correct finite-field arithmetic is checked against Fermat and Frobenius
  identities, inversion, distributive trace, and exhaustive multiplication
  commutativity over each supported field.
- For all nine fields, the fiber balance checks prove the tested Fourier
  matrices orthogonal at all nonzero row differences.
- Deterministic varied-form tests exercise dimensions 1 and 2, changing
  couplings, phases, and cyclotomic-valued weights.
- Odd k=3,5,7 sharpness certificates compare exact reduced cyclotomic
  coefficients to the predicted phase times q^{d(k+1)/2}.
- Degenerate matrix mutants produce coherent all-one sums exceeding
  the purported nondegenerate estimate.
- A deliberately understated T bound is rejected before evaluation.

## Interpretation for MathCan, DataGoblin, and finite-field crypto

This supplies finite verifier-grounded repair tasks where an agent must
identify whether a form is nondegenerate, the character is nontrivial,
the weights obey T, and the predicted exponent is sharp. The symbolic
odd-length family is a useful adversarial test for purported
improvements to Lemma 3.

For cryptographic proof systems, these certificates are reusable for
checking exact finite Fourier gadgets over small extension fields.
They do not imply a new ECDLP algorithm, a weakness in elliptic-curve
signatures, or an improved counting algorithm for arbitrary curves.

**Follow-up formalization:** Mathlib-level generic additive-character
orthogonality, its finite Hilbert-space operator norm, and the
positive-multiplicity power-sum spectral bound. The etale/Gysin
premises remain separate obligations.
