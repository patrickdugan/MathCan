# NOR-09: asynchronous two-basin history compactification from certified natural inputs

**Research note, November 15, 2026.** This is a new synthesis within NOR-01–08. It combines two independently verified source-to-attractor capture witnesses, genuinely nonlinear local contraction, and the earlier OpenAI Math #094 finite-set \(L_p\) embedding. The analytic results are proved below, and the discrete metric-clipping core is Lean-checked in MathCan/NOR09Asynchronous.lean. Literature priority remains unverified.

## 1. The executed source evidence

The unmodified 1,000-parameter trained RRC-25 GRU defines a real-analytic zero-input transition \(F:\mathbb R^{12}\to\mathbb R^{12}\) by interpreting its checkpoint decimal weights as exact rational real numbers. Its model SHA-256 is

54f225f2a61c52fee5a740576eaab3bcbc5280a595fc1ac1ac115ec8ac26c41b.

The earlier campaigns established, through separate host CI runs:

- **First source:** a public signed-family RRC-25 input produces hidden state \(h^{(1)}\) after nine source feature rows. NOR-06B's rational trace certifies that \(F^{1308}(h^{(1)})\) belongs to the first ball \(B(c_1,R_1)\), \(R_1=10^{-11}\). NOR-04 certifies \(F^{12}\) contracts on that ball with \(K_1=0.928242792263\). NOR-05 proves the unique block fixed point \(p_1\) satisfies \(F(p_1)=p_1\).
- **Second source:** a different public squared-family RRC-25 input produces \(h^{(2)}\). NOR-08B's rational trace certifies that \(F^{660}(h^{(2)})\in B(c_2,R_2)\), \(R_2=10^{-6}\). The enlarged NOR-08A ball has a uniform \(F^{24}\) contraction factor \(K_2=0.8303094953723295\) and its unique fixed point \(p_2\) satisfies \(F(p_2)=p_2\).
- **Separate anchors:** the two closed balls are disjoint, with a certified lower bound \(g>5.020911335789842\) on the Euclidean distance between any point in the first ball and any point in the second.

Primary executed receipts: [signed capture](https://github.com/MoralityLabAI/Compactification-Theory/actions/runs/43695479529), [second-basin radius](https://github.com/MoralityLabAI/Compactification-Theory/actions/runs/43699717963), [squared capture](https://github.com/MoralityLabAI/Compactification-Theory/actions/runs/43700133484), and [two-basin code gap](https://github.com/MoralityLabAI/Compactification-Theory/actions/runs/43700705224).

The two capture clocks differ. Align them by **elapsed 24-step blocks after each source's own certified capture**, rather than asserting that both sources enter their balls on the same original recurrence step.

## 2. Exact nonlinear tail amplitudes

Let \(T_1=1308\), \(T_2=660\), and \(z_i(m)=F^{T_i+24m}(h^{(i)})\). The signed capture supplies exact rational bounds
\[
D_1=\frac{957509766970587967489}{10^{32}},\qquad
\epsilon_1=\frac{9579}{1562500000000000000000000000000},
\]
so that \(\|z_1(0)-c_1\|\le D_1+\epsilon_1\). The squared capture supplies
\[
D_2=\frac{2019911314217696479857059}{2500000000000000000000000000000},
\qquad
\epsilon_2=\frac{11725051219}{50000000000000000000000000000000},
\]
giving \(\|z_2(0)-c_2\|\le D_2+\epsilon_2\).

Let \(s_i\) be the corresponding certified block-center residual bound from NOR-04/NOR-08, and define
\[
\delta_i=\frac{s_i}{1-K_i},\quad
A_i=D_i+\epsilon_i+\delta_i,\quad
\rho_1=K_1^2,\quad
\rho_2=K_2.
\]
Then Banach's theorem gives \(\|c_i-p_i\|\le\delta_i\). The 24-step progression stays within the respective invariant balls and satisfies
\[
\|z_i(m)-p_i\|\le A_i\rho_i^m,\qquad
\boxed{\|z_i(m)-c_i\|\le A_i\rho_i^m+\delta_i=:B_i(m).}\tag{1}
\]
This uses the true nonlinear recurrence, rather than repeated powers of a single Jacobian.

Numerically, the **certified upper bounds** obey

| Extra 24-step blocks \(m\) | \(B_1(m)\) | \(B_2(m)\) | \(2\max(B_1,B_2)\) |
| ---: | ---: | ---: | ---: |
| 0 | \(9.6082\times10^{-12}\) | \(8.0797\times10^{-7}\) | \(1.6160\times10^{-6}\) |
| 32 | \(9.824\times10^{-14}\) | \(2.1042\times10^{-9}\) | \(4.2083\times10^{-9}\) |
| 64 | \(1.7230\times10^{-14}\) | \(5.4797\times10^{-12}\) | \(1.0960\times10^{-11}\) |
| 96 | \(1.6540\times10^{-14}\) | \(1.4271\times10^{-14}\) | \(3.3079\times10^{-14}\) |
| 128 | \(1.6534\times10^{-14}\) | \(3.7164\times10^{-17}\) | \(3.3067\times10^{-14}\) |

These decimal numbers are display roundings of formulas independently checked over exact rational fractions. The first center has an irreducible certified offset \(\delta_1\approx1.65334\times10^{-14}\) from the unknown true fixed point. Using the *rational centers* as clipping anchors consequently produces a nonzero certificate floor \(2\max(\delta_1,\delta_2)\approx3.30667\times10^{-14}\). This is a limit of the available center certificates and is not a physical lower bound on achievable compression error.

## 3. Constructive two-anchor clipping theorem

Fix any \(M\ge1\). Pool the **finite captured prefix**
\[
\mathcal P_M=\{c_1,c_2\}\cup
\{z_1(0),\ldots,z_1(M-1),z_2(0),\ldots,z_2(M-1)\}.
\]
Choose any representation of these finite states with pairwise additive metric distortion at most \(E_M\), including the two anchor states. For every \(m\ge M\), replace \(z_i(m)\) by the existing image of its *own* rational anchor \(c_i\). The clocks are independently indexed by the captured block number.

**Theorem A (asynchronous two-basin all-horizon metric bound).** For **all** pairs of block-sampled times from either captured stream,
\[
\boxed{
\left|d_{\mathrm{encoded}}-d_{\mathrm{true}}\right|
\le E_M+2\max\{B_1(M),B_2(M)\}.
}\tag{2}
\]
*Proof.* For two finite observations, the discrepancy is at most \(E_M\). Replacing one late state by its anchor perturbs its true distance to any other point by at most \(\|z_i(m)-c_i\|\le B_i(M)\), using the reverse triangle inequality. Replacing both endpoints changes their true pair distance by at most \(B_i(M)+B_j(M)\le2\max B\). The images of the anchors already belong to the finite representation, so their pair-distance errors are included in \(E_M\). The argument applies whether both endpoints belong to the same basin or different basins. \(\square\)

For the *identity Euclidean representation* of the observed 12-dimensional states, \(E_M=0\). At \(M=64\), the infinite-horizon tail-clipping error certificate is less than \(1.2\times10^{-11}\). The original hidden dimension remains twelve, and only the finite prefix plus two anchor vectors needs storage.

For an existential lower-coordinate representation, normalize a Gaussian linear functional to embed the real Hilbert state space isometrically into real \(L_p\). OpenAI Math #094 then embeds the at-most-\(2M+2\) finite points into \(\ell_p^d\), with
\[
d\le
\exp\left(C_{p,D}(\log(2M+2))^{\gamma(p)}\right),\quad
\gamma(p)=
\begin{cases}2-p&1<p<2,\\1-2/p&p>2.\end{cases}
\]
The resulting finite-prefix additive distortion \(E_M\) remains separately accounted for in (2). The existence theorem does not provide a general efficient construction; a stochastic Gaussian sketch must be measured independently.

## 4. The necessary extra terminal bit

Both \(z_1(m)\) and \(z_2(n)\) remain inside their **distinct** invariant balls at every captured 24-step checkpoint. Thus, for arbitrary \(m,n\ge0\),
\[
\boxed{\|z_1(m)-z_2(n)\|_2\ge g>5.020911335789842.}\tag{3}
\]
If a representation assigns the *same* terminal code to both states, their encoded distance is zero. Any additive metric distortion promise strictly below \(g\) therefore requires different terminal codes, or at least **one binary basin label**. This follows directly from the certified geometric separation and the general MathCan NOR-08 injectivity theorem.

This lower bound and the separate-anchor construction jointly delimit the history representation: late individual tails can be replaced by their anchors at a certified small error, while one shared terminal anchor would lose a macroscopically large cross-basin distance.

## 5. Formal, experimental, and epistemic boundaries

The discrete natural-number metric replacement inequalities, including independently captured stream time indices, are formalized in [MathCan/NOR09Asynchronous.lean](../../MathCan/NOR09Asynchronous.lean). The full real Banach and Gaussian \(L_p\) arguments are written mathematics and inherit the previously executed rational certificates; the new two-source exact fraction schedule runs in [Compactification-Theory NOR-09](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor09-certified-dual-history-20261115/research/nor01_numerical_orbit_sketch).

The specific numerical error budgets apply to **24-step checkpoint samples** after each independently certified source capture. All-integer-step trajectories admit separate bounds through NOR-05 and the NOR-07 period-one proof; extending the sharp numerical values of (1) to each residue modulo 24 requires additional validated per-residue Jacobian bounds.

Both sources were built from public RRC-25 input features followed by a declared zero-input intervention. This proves a particular geometric capability of the original trained recurrent checkpoint. Native theorem-proving success, model safety classifications, semantic feature identity and generalization to larger trained reasoners require separate experiments.
