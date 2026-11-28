# SPC-02: robust sparse phase observability and deferred-query state cost

**15 November 2026.** A new finite-dimensional mathematical synthesis extending
[SPC-01](SPC-01.md). Theorems 1–4 and Proposition 5 below are derived here with proofs. No
independent priority review has been conducted. The arbitrary-complex-field
proofs are paper arguments; `MathCan/SpectralStability.lean` formally checks
finite-field specializations and a general injectivity lemma.

## Source pair and its precise role

* OpenAI Mathematics family **#129**, [*An exponential two-way deterministic state lower bound for one-way liveness*](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026), 25 September 2026. Its use here is the **deferred-context distinguishability** perspective: stored states must separate inputs whose future queried answers differ. The source's two-way automaton bound and its matching-monoid machinery are *not* asserted for recurrent neural networks.
* OpenAI Mathematics family **#130**, [*Finite tensor savings and exact Fourier circuits*](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026), 25 September 2026. Its role is the exact Fourier-coordinate/tensor viewpoint. Its nonuniform Fourier circuit-size improvement is *not* used as a runtime or compression guarantee here.

Source snapshot `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

## 1. Measurement model and norm convention

Take integers \(n=md\), \(m,d\ge1\), and the unnormalized forward DFT
\(a_f=\sum_{t=0}^{n-1}x(t)e^{-2\pi ift/n}\). A phase-\(s\) channel records
\(y_s(v)=x(s+dv)\) for \(v\in\mathbb Z_m\). For \(j\in\mathbb Z_m\), put
\(a_{j,r}=a_{j+rm}\), \(r\in\mathbb Z_d\), and define
\[
 b_{s,j}=d\,e^{-2\pi i js/n}\widehat y_s(j)
 =\sum_{r=0}^{d-1}e^{2\pi i sr/d}a_{j,r}.
 \tag{1}
\]

Let \(S\subset\mathbb Z_d\) be the ordered phase schedule, \(q=|S|\), and
\(V_S(s,r)=e^{2\pi i sr/d}\). Thus the measurement map, after invertible
DFT and dephasing, splits into \(m\) independent \(q\times d\) blocks.
All norms below are Euclidean. A spectrum is *block-\(k\)-sparse* if at
most \(k\) coefficients are nonzero in each residue class \(j\).

The noiseless identifiability threshold in SPC-01 is
\(q\ge p:=\min(2k,d)\) for consecutive phases. We now quantify stability.

## 2. Theorem 1: uniform Vandermonde noise margin

Let \(1\le k\le d\), \(p=\min(2k,d)\), and suppose the measured phases
contain \(0,1,\dots,p-1\). Define
\[
 \delta_d=2\sin(\pi/d),\qquad
 \gamma_{d,p}=\begin{cases}
 \delta_d^{p(p-1)/2}/p^{p-1}, &p<d,\\
 \sqrt d, &p=d.
 \end{cases}
 \tag{2}
\]
When \(d=1\), the second case defines \(\gamma=1\).

**Theorem.** For every complex vector \(h\in\mathbb C^d\) supported on
at most \(p\) columns,
\[
 \boxed{\|V_S h\|_2\ge\gamma_{d,p}\|h\|_2.}\tag{3}
\]
Consequently, if \(a,a'\) are block-\(k\)-sparse and \(B_S\) denotes
the direct sum of the \(m\) dephased alias maps, then
\[
 \boxed{\|B_S(a-a')\|_2\ge\gamma_{d,p}\|a-a'\|_2.}\tag{4}
\]

**Proof.** For \(p<d\), extend the support of \(h\) to any \(p\)
frequencies \(r_1,\dots,r_p\). The square submatrix using the first
\(p\) phases is Vandermonde on \(z_i=e^{2\pi i r_i/d}\). Its determinant has
magnitude \(\prod_{i<j}|z_j-z_i|\). The distance between any two
distinct \(d\)th roots is at least \(\delta_d\), hence
\(|\det V|\ge\delta_d^{p(p-1)/2}\). Every matrix entry has modulus
one, so \(\|V\|_2\le\|V\|_F=p\). The product of all \(p\) singular values
equals \(|\det V|\); bounding the largest \(p-1\) factors by \(p\)
gives \(\sigma_{\min}(V)\ge\gamma_{d,p}\). Restricting to a
smaller support by zero extension preserves its Euclidean norm. Extra
phase rows only increase the measurement norm. For \(p=d\), the
full \(d\)-point Fourier matrix satisfies \(V^*V=dI\). Apply the
single-block bound to the difference in each residue class and add
squares over \(j\). QED.

The bound can be extremely conservative for large \(d\). It is a
uniform analytic certificate, and not a condition-number estimate
obtained from a finite floating-point search. If \(q<p\), SPC-01
constructs exact collisions among distinct \(k\)-sparse spectra, so
**no positive uniform gain** exists at that probe budget.

### Corollary: full-period reconstruction from noisy samples

Suppose the observed time-domain matrix has error \(\eta\), with
\(\|\eta\|_2\le\varepsilon\). Let \(\widetilde a\) be any
block-\(k\)-sparse fit whose observed residual is no larger than
\(\varepsilon\), and let \(\widetilde x\) be its inverse \(n\)-point DFT.
Then
\[
 \boxed{\|\widetilde x-x\|_2\le
            \frac{2\sqrt d}{\gamma_{d,p}}\varepsilon.}\tag{5}
\]
**Proof.** The observed-frequency DFT in each \(m\)-sample channel
multiplies the Euclidean error norm by \(\sqrt m\), dephasing is
unitary, and the factor \(d\) in (1) multiplies the noise by \(d\).
Thus the dephased measurement noise norm is \(d\sqrt m\varepsilon\).
By the triangle inequality, the difference between the fitted and
true forward measurements is at most \(2d\sqrt m\varepsilon\).
Apply (4) and unnormalized Parseval
\(\|\widetilde x-x\|=\|\widetilde a-a\|/\sqrt n\) with
\(n=md\). QED.

When the true trajectory \(u\) is only approximately period-\(n\),
choose a periodic proxy \(x\) with \(\|u-x\|\le\rho\) on the analyzed
window. For a sample disturbance \(\nu\) of norm at most
\(\varepsilon\), a proxy-based estimate obeys
\[
 \|\widetilde x-u\|\le \rho+
 \frac{2\sqrt d}{\gamma_{d,p}}(\rho+\varepsilon).\tag{6}
\]
The fitted periodic proxy and its residual must be reported. In
particular, a low rank or dark phase trace under a high-residual proxy
provides weak evidence about the actual recurrent dynamics.

## 3. Theorem 2: sharp one-frequency stability

For \(k=1\), \(d\ge2\), use phases \(0,1\). Among all vectors
supported on at most two frequencies, the exact least singular gain is
\[
 \boxed{\inf_{\|h\|_2=1,\ |\operatorname{supp}h|\le2}
 \|V_{\{0,1\}}h\|_2=2\sin\frac{\pi}{2d}.}\tag{7}
\]

**Proof.** A two-column submatrix on distinct frequencies \(f,g\) is
\(M=\bigl(\begin{smallmatrix}1&1\\z_f&z_g\end{smallmatrix}\bigr)\).
Its Gram matrix has diagonal entries \(2\) and off-diagonal
\(1+\overline z_f z_g\), so its least eigenvalue is
\(2-|1+e^{2\pi i(g-f)/d}|\)
\(=2-2|\cos(\pi(g-f)/d)|\). This is minimized at circular
frequency separation one, giving \(4\sin^2(\pi/(2d))\).
A one-column submatrix has singular value \(\sqrt2\), which is
at least this value. The adjacent pair attains equality. QED.

This explicit \(\Theta(d^{-1})\) inverse margin shows that exact
one-sparse identifiability alone gives a poor noise guarantee when
frequency spacing becomes very fine.

## 4. Theorem 3: arithmetic-progression invariance and failures

Let the phase schedule be \(S=(s_0+at)_{t=0}^{q-1}\pmod d\),
where \(q\le d\). If \(\gcd(a,d)=1\), the matrix \(V_S\) is obtained
from \(V_{0:q-1}\) by a column permutation and multiplying each column
by a unit complex scalar. Therefore the full set of singular values
of every support-size submatrix is preserved up to relabeling, and
\[
 \boxed{\gamma_\star(S,p)=\gamma_\star(\{0,\dots,q-1\},p),}\tag{8}
\]
where \(\gamma_\star\) denotes the exact worst gain over supports of
size at most \(p\).

If \(g=\gcd(a,d)>1\), the columns with indices \(r\) and
\(r+d/g\) are proportional: their ratio is a constant factor
\(e^{2\pi i s_0/g}\) over all sampled phases. Two one-sparse
frequency assignments, with appropriately rescaled complex amplitudes,
therefore yield identical measurements, even if \(q\) is arbitrarily
large relative to the sparse-identification requirement. QED.

This result explains why merely spreading arithmetic-progression
samples across the period cannot improve the *worst-case* condition
number. Non-arithmetic phase choices can improve it. For composite
\(d\), poorly chosen irregular schedules may also destroy full spark.

## 5. Theorem 4: deferred-phase distinguishability and finite memory

Define the **fixed-amplitude family** \(\mathcal F_{m,d,k}\) by setting
each alias class's coefficients \(a_{j,r}\in\{0,1\}\) to have exactly
\(k\) entries equal to one. Its cardinality is
\[
 |\mathcal F_{m,d,k}|=\binom{d}{k}^{m}.\tag{9}
\]

Every element of this family has the **same entire phase-zero channel**:
(1) yields \(b_{0,j}=k\) for every \(j\). The family is invisible to
phase-zero spectral-support classification despite comprising
\(\binom dk^m\) distinct underlying spectra.

Consider a deterministic device that first reads the original spectrum,
stores a state \(\mathrm{enc}(a)\), then must exactly answer an arbitrarily
chosen future query \((s,j)\mapsto b_{s,j}(a)\) using only the state.
The entire \(d\)-point Fourier transform in each alias class is
invertible, hence distinct family members differ in at least one
possible future query. Therefore \(\mathrm{enc}\) is injective and
\[
 \boxed{\#\mathrm{States}\ge\binom{d}{k}^{m},\qquad
 \mathrm{storage\ bits}\ge\left\lceil
 m\log_2\binom{d}{k}\right\rceil.}\tag{10}
\]

**Proof.** If two distinct inputs were mapped to the same stored state,
all later query replies would coincide. Fourier inversion then forces
all their original coefficients to coincide, a contradiction. The
state count and bit bound follow by pigeonhole counting. QED.

For two different members of \(\mathcal F_{m,d,k}\), the squared
coefficient-vector separation is at least two: distinct supports of
fixed cardinality require an element leaving and another entering.
Under the consecutive or coprime-progressive probe budget \(q\ge p\),
Theorem 1 implies that their time-sampled observations are at least
\[
 \frac{\sqrt2\,\gamma_{d,p}}{d\sqrt m}
\tag{11}
\]
apart in norm. Thus the whole family admits robust nearest-neighbor
identification when the total measurement-noise radius is strictly
smaller than \(\gamma_{d,p}/(\sqrt2 d\sqrt m)\). Storing the
identity for all future queries still requires (10) states.

These are explicit *finite-class* memory bounds for exact deferred
queries. They do **not** imply the two-way automaton lower bound of
OpenAI family #129 for a neural system, and they do not count the
continuous precision needed to store unrestricted complex amplitudes.

## 6. Reproducible finite schedule search and controls

The `LoopedTransformers` companion code enumerates all support-size
\(p=2k\) submatrices and computes the smallest singular value. For
\(d=7,k=2,q=4\), there are \(\binom74=35\) phase schedules and
\(\binom74=35\) four-column supports, or **1,225** SVDs.

| Schedule | Numerically observed worst gain | Meaning |
|---|---:|---|
| `(0,1,2,3)` | 0.2961051161 | Conventional consecutive probes |
| `(0,1,2,4)` | 0.6311266657 | A best finite schedule in the exhaustive search |
| `(2,4,5,6)` | 0.6311266657 | Another tied best schedule |

The optimized finite schedule improves the least gain by a factor
**2.131428**. This is a floating-point numerical certificate over a
small bounded search, not a machine-checked proof of optimality.
For the same \(d,k\), Theorem 1 yields the conservative analytic
floor \(\gamma_{7,4}\approx0.0066717574\) for consecutive probes.

For composite \(d=6\), the irregular four-phase schedule
`(0,1,2,4)` has a rank-deficient four-column minor. Consecutive
`(0,1,2,3)` retains full spark. The `MathCan` exact arithmetic tests
reproduce a zero minor over \(\mathbb F_7\), separate from complex
floating-point SVD.

A constructed \(m=3,d=7,k=2\) signal with sample noise \(10^{-6}\)
exercises an exhaustive support-fit decoder. A held-out nonperiodic
drift control measures the residual from the best periodic proxy.
The CLI accepts a depth-first `.npy` or `.npz` activation trace, including
`(batch, depth, features)` arrays, and reports its periodization residual
and the fraction of power left after retaining \(k\) modes per alias
class. These diagnostics use thresholds and are **not proofs** that a
real transformer is approximately periodic or block-sparse.

## 7. Formal boundary and next falsification

`MathCan/SpectralStability.lean` kernel-checks finite F\(_7\)
primitive-root orthogonality, the two coprime singleton codes, a
noncoprime alias collision, and a generic deferred-query injectivity
lemma, using `decide` and ordinary Lean equality reasoning. Its
nontrivial memory lemma is parameterized over arbitrary state types.
A separate arithmetic oracle enumerates 15 two-support subsets in
six frequencies, and all 225 independent two-block support choices.

The **general complex-field singular-value theorem**, exact
state-cardinality bound for the full \(m,d,k\) family, and noise
stability of arbitrary nonperiodic network activations are not
represented as Lean-kernel results.

Priority experimental question: on frozen looped-model hidden-state
traces, does the measured periodic-proxy residual stay low enough for
(5) to be informative? Compare optimized and consecutive schedules
under matched noise, with held-out phase prediction, and label every
run by its spectral sparsity tail. An excess-error result under
matched residual and noise would falsify the proposed applicability of
the phase-sparse model to that network family.


## 8. Proposition 5: DC-invariant periodic residual identity

Let `H` be any finite-dimensional real or complex Hilbert space of
length-`T` multichannel traces. Assume `n` divides `T`. Let `P` be the
orthogonal projection onto traces periodic with period `n`, and `C`
the orthogonal projection onto traces constant over time. Since
`range(C)` is contained in `range(P)`, we have `PC=CP=C`.
For a trajectory `u` write

\[
\rho=\frac{\|(I-P)u\|}{\|u\|},\quad
\rho_{\mathrm{dyn}}=\frac{\|(I-P)(u-Cu)\|}{\|u-Cu\|},\quad
\alpha=\frac{\|Cu\|^2}{\|u\|^2}.
\]

**Proposition.** Whenever `u` has a nonzero time-varying component,

\[
\boxed{\rho_{\mathrm{dyn}}=\frac{\rho}{\sqrt{1-\alpha}}.}
\tag{12}
\]

**Proof.** The nested projections satisfy `(I-P)C=0`, so
`(I-P)(u-Cu)=(I-P)u`. Orthogonality of `C` gives
`||u-Cu||²=||u||²-||Cu||²`. Divide the same residual norm by each
of the two trajectory norms. QED.

A large constant prompt embedding can make `alpha` approach one,
and hence make an apparently small raw periodic residual uninformative
about the recurrence's changing component. The native LoopedChase
smoke now records both residuals, their DC-energy ratio, and the
centered spectral-sparsity tail. This identity is an exact linear
algebra statement independent of the Fourier sparsity premise.
