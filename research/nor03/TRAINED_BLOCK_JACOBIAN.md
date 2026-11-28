# NOR-03: verified block Jacobians of nonlinear recurrent maps

**Research status (November 15, 2026):** A mathematical theorem, its proof, and a source-locked rational numerical-range certificate applied to the frozen RRC-25 trained GRU. Novelty is claimed only as a derivation in our program; priority over the literature remains unverified. The analytic theorem uses external OpenAI Math #094 and #325. The finite arithmetic certificate does not, by itself, establish semantic understanding, native proof-search performance, or global nonlinear convergence.

Sources are locked to OpenAI's [Subpolynomial dimension reduction in Lp](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Subpolynomial-dimension-reduction-in-Lp-September-23-2026/build/paper.tex) and [complete Crouzeix inequality](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex). The previous NOR-02 theorem is [here](../nor02/FILTERED_ORBIT_CURVATURE.md).

## Theorem: interval-source block numerical range and quadratic shadowing

Let \(U\subset\mathbb R^n\) be convex, let \(F:U\to U\) be \(C^2\), and suppose
\[
\|D^2 F(h)[u,v]\|_2\le M\|u\|_2\|v\|_2,\qquad h\in U.
\]
Fix an orbit \(h_{j+1}=F(h_j)\) for \(j=0,\dots,L-1\), write \(J_j=D F(h_j)\), and let rational matrices \(B_j\) with certified errors
\[
\|J_j-B_j\|_2\le\epsilon_j,\qquad
\|B_j\|_2+\epsilon_j\le\nu_j
\]
be given. Put \(B=B_{L-1}\cdots B_0\), \(A=D(F^L)(h_0)=J_{L-1}\cdots J_0\), \(\epsilon_*=\max_j\epsilon_j\), and \(\nu_*=\max_j\nu_j\).

**Theorem 1 (block disk from a nonlinear orbit).**
\[
\boxed{\|A-B\|_2\le L\nu_*^{L-1}\epsilon_*=:E_L.} \tag{1}
\]
For any rational \(a>0\), choose a rational \(b\) with
\[
b\ge\sqrt{\sum_{i,k}(B_{ik}-a\delta_{ik})^2}+E_L.
\]
Then the **complex** numerical range of the true derivative satisfies
\[
\boxed{W_{\mathbb C}(A)\subseteq\overline D(a,b).} \tag{2}
\]
If \(q=a+b<1\), this produces a rigorous *one-block* radial decay gate even when the original one-step Jacobians are transiently amplifying.

**Proof.** A telescoping product identity writes \(A-B\) as a sum of \(L\) terms, each with one factor \(J_j-B_j\) and the other factors chosen from \(J_k\) or \(B_k\). Taking norms yields (1). For every complex unit vector \(u\),
\[
|u^*Au-a|=|u^*(A-aI)u|
\le\|A-aI\|_2\le\|B-aI\|_F+E_L\le b.
\]
This proves (2), including the complexification required by Crouzeix. \(\square\)

**Theorem 1b (direct interval-product numerical-range certificate).** If each entry of every true Jacobian \(J_j\) is contained in a closed real rational interval \(I_{j,ik}\), form the interval product
\[
I=I_{L-1}\cdots I_0
\]
by usual outward-rounded interval addition and multiplication. Denote its entry bounds by \(\underline I_{ik},\overline I_{ik}\). For each rational \(a>0\), define
\[
c_{ik}=\max\{|\underline I_{ik}-a\delta_{ik}|,
                   |\overline I_{ik}-a\delta_{ik}|\}.
\]
Then
\[
\boxed{W_{\mathbb C}(D(F^L)(h_0))\subseteq
\overline D\left(a,\sqrt{\sum_{i,k}c_{ik}^2}\right).}\tag{2a}
\]
**Proof.** Interval arithmetic encloses every entry of the actual product by induction on its factors, including all signed cancellations. Hence \(|A_{ik}-a\delta_{ik}|\le c_{ik}\). Squaring and summing controls the Frobenius norm, which dominates the operator norm, and therefore the complex numerical range. Rounding the final square root **upward** preserves validity. \(\square\)

Equation (2a) can be substantially tighter than (1) when global norm bounds obscure nonnormal cancellation. The implementation computes both and retains their minimum. The direct method is still a sufficient enclosure and can fail even for a stable true block.

**Theorem 2 (finite nonlinear shadowing budget).** Suppose \(h_0+e\in U\), \(\|e\|\le\delta_0\), and the segment of each perturbed and reference state remains in \(U\). Define by exact nonnegative recurrences
\[
\begin{aligned}
\delta_{j+1}&=\nu_j\delta_j+\tfrac M2\delta_j^2,\\
R_0&=0,\qquad
R_{j+1}=\nu_j R_j+\tfrac M2\delta_j^2.
\end{aligned}
\]
Then
\[
\|F^L(h_0+e)-F^L(h_0)\|_2\le\delta_L
\]
and, with the **true block derivative** \(A\),
\[
\boxed{
\|F^L(h_0+e)-F^L(h_0)-Ae\|_2\le R_L.}\tag{3}
\]

**Proof.** At time \(j\), Taylor's integral remainder is bounded by \(M\|\Delta_j\|^2/2\). This gives \(\|\Delta_{j+1}\|\le\nu_j\|\Delta_j\|+M\|\Delta_j\|^2/2\). For \(E_j=\Delta_j-(J_{j-1}\cdots J_0)e\), the same Taylor expansion yields \(\|E_{j+1}\|\le \nu_j\|E_j\|+M\delta_j^2/2\). Induction proves (3). \(\square\)

These estimates allow arbitrary nonnormal intermediate Jacobians. Their usefulness depends on the computable \(\nu_j\), \(M\), and interval widths. A large finite nonlinear remainder budget is a legitimate upper bound, not evidence of practical small error.

## OpenAI pairing on the true trained derivative

If (2) yields \(0<a\), \(0<b\), and \(q=a+b<1\), the sharp complete Crouzeix theorem #325 gives, for **any** matrix-valued polynomial \(P\),
\[
\|P[A]\|_2\le2\sup_{z\in\overline D(a,b)}\|P(z)\|_2.
\]
For the noncommuting coefficient filter
\[
P_r(z)=(z-q)^r
\begin{pmatrix}0&1\\z&0\end{pmatrix}
\]
and all \(t\ge1\), the NOR-02 disk geometry yields
\[
\boxed{
\|[z^tP_r(z)][A]\|_2
\le 2 (b/a)^{r/2}q^{t+r}
\sqrt{\frac{t^t r^r}{(t+r)^{t+r}}}.}\tag{4}
\]
The full complex Hilbert tensor space can be realified, then embedded isometrically into real \(L_p\) by a normalized Gaussian linear functional. Paper #094 gives finite-set distortion-\(D\) \(\ell_p^d\) embeddings of \(T+1\) *frozen tangent states* with
\[
d\le\exp(C_{p,D}(\log(T+1))^{\gamma(p)})
\]
for \(1<p<\infty\), \(p\ne2\). NOR-02's optimized all-horizon metric stitching applies to these tangent states.

**Scope boundary:** \(A=D(F^L)(h_0)\) is the derivative of one actual \(L\)-step nonlinear block, but \(A^t\) describes repeatedly applying the **frozen** linearized block. Successive nonlinear blocks generally have different Jacobians. Equation (3) controls the first full nonlinear block; a global all-depth nonlinear transfer requires an invariant tube or a source-certified derivative-variation budget over successive blocks. The paper pairing alone does not supply that extra hypothesis.

## Certified computational instantiation: trained RRC-25 GRU

The [companion NOR-03 program](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/nor01-numerical-orbit-sketch-20261115/research/nor01_numerical_orbit_sketch/trained_gru_cert.py) loads the original 1,000-weight recurrent checkpoint, checks its committed source SHA-256 inventory, and uses all nine public 8-feature rows for any tested RRC-25 case. For its canonical trained-source witness, it runs eight zero-input GRU transitions from hidden zero before taking the next \(L=12\) transitions as the **actual nonlinear block**.

The GRU has twelve hidden dimensions. At zero input, write
\[
r_i=\sigma(b^r_i+R_i h),\quad
z_i=\sigma(b^z_i+Z_i h),\quad
n_i=\tanh(b^n_i+r_i(b^{hh,n}_i+N_i h)),\quad
F_i(h)=z_i h_i+(1-z_i)n_i,
\]
where the input-hidden and hidden-hidden biases match the PyTorch checkpoint. For \(h\in[-1,1]^{12}\), this cube is invariant under \(F\).

**Global analytic second-derivative bound.** Let \(r_i^*=\|R_i\|_2\), \(z_i^*=\|Z_i\|_2\), \(n_i^*=\|N_i\|_2\), \(V_i=|b^{hh,n}_i|+\|N_i\|_1\). Set
\[
G_i=n_i^*+\tfrac14V_i r_i^*,\qquad
H_i=\tfrac14 V_i(r_i^*)^2+\tfrac12r_i^*n_i^*,\\
M_i=2G_i^2+H_i+\tfrac12(z_i^*)^2
  +\tfrac12 z_i^*(1+G_i),\quad M=\sum_i M_i.
\]
The classical derivative bounds \(|\sigma'|\le1/4\), \(|\sigma''|\le1/4\), \(|\tanh'|\le1\), \(|\tanh''|\le2\) imply the required bilinear Hessian bound on the invariant cube. Every row norm is enclosed from its exact checkpoint decimal weights by an upward rational square root.

**Exact interval transport.** Each JSON decimal checkpoint weight is treated as a rational. The transcendental functions are evaluated with rational bounds. For \(x\ge0\), if \(n+2>x\),
\[
S_n=\sum_{k=0}^n\frac{x^k}{k!},\quad
S_n\le e^x\le
S_n+\frac{x^{n+1}/(n+1)!}{1-x/(n+2)}.
\]
Negative exponentials are enclosed by reciprocal intervals; sigmoid and tanh follow by monotonicity. The entire nine-step input prefix and zero-input continuation are propagated as rational intervals. At each of the next twelve states, a rational center and rational Jacobian approximation are computed; interval uncertainty plus the global \(M\)-bound covers the exact analytic Jacobian, including the error of rounding a hidden-state interval to its center. Matrix products are formed over \(\mathbb Q\) and independently as direct outward-rounded interval products; every Frobenius square root rounds upward. The final enclosing disk radius \(b\) is rational and uses the tighter of the two proven envelopes.

Six new deterministic post-training RRC-25 test-family inputs are generated directly, one per family, with independent seeds `compound25.SEED+903900+1009*i` and an explicit first-valid-source-case rule. This avoids generating unrelated negative and collision cohorts during a matrix-analysis job. The experiment uses public features only and fits no parameters or projections. The code checks distinct visible case contents within this cohort; overlap against the original 720 training examples has not been exhaustively audited. Each case retains its source-family label, hashed identifier, original native logit parity, and a certified pointwise block disk in the GitHub Actions artifact. The positive/negative contractivity fields are evaluated by exact rational comparison of \(a+b\) against one.

The 8-step local tangent at hidden zero was found numerically to be strongly amplifying, while the later zero-input local tangent had contracting powers. The exact-rational CI is the gate for transferring that observation to the true twelve-step block derivative. Report both successful and unsuccessful families; an unsuccessful disk enclosure is a method failure rather than a theorem violation.

## Independent verification and restrictions

- Checkpoint: `research/rrc_compactification/results/rrc25_recurrent.json`, expected SHA-256 `54f225f2a61c52fee5a740576eaab3bcbc5280a595fc1ac1ac115ec8ac26c41b`.
- Input features: historical Python float values from the public feature generator are lifted as exact decimal rationals via `str(float)`. The interval model certifies this real-analytic lift. The source PyTorch training was float32; portable Python replay remains a separately checked finite-precision computation.
- Whole orbit: finite-state boxes are certified by rational operations; the general analytic inequalities (1)–(4) have paper-level proofs. The Lean library currently covers the discrete NOR-01/02 stitching lemmas only.
- A disk enclosure may be conservative. The condition \(a+b<1\) certifies sufficient stability; failure to meet it does not prove divergence.
- Nonlinear remainder (3) is valid for a single block and perturbations that remain in the invariant cube, which the GRU guarantees for unit-cube inputs. No assertion of downstream trained classification improvement follows from this geometry.

## Completed source-locked empirical certificate (15 November 2026)

The companion [NOR-03 completed verification report](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/nor01-numerical-orbit-sketch-20261115/research/nor01_numerical_orbit_sketch/NOR03_RESULTS.md) records a successful Python CI run at [Actions #43691049653](https://github.com/MoralityLabAI/Compactification-Theory/actions/runs/43691049653). Rational outward-interval products certify a contracting 12-step derivative disk for **five of six** post-training public source-family hidden states after eight artificial zero-input steps: signed q=0.950759, sparse q=0.960809, product q=0.731709, rational q=0.576830 and late_source q=0.960411. The squared family yields a sufficient-disk upper bound q=1.384528, which leaves its contraction undecided. The canonical trained-zero eight-step warmup yields q=0.937536 for the following twelve-step block. At warmup 32, all six family enclosures fail the sufficient disk test as their interval widths compound. These results apply to source-locked decimal-rational lifted checkpoint weights and to the true *one-block derivative* only.
