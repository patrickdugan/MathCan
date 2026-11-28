# NOR-08: basin-label capacity of an all-horizon recurrent compactifier

**15 November 2026.** New mathematical synthesis in the NOR-01–07 program. This extends the two-basin terminal-code obstruction to an arbitrary finite set of recurrent attractors. Its combinatorial core is Lean-checked in MathCan/BasinCodes.lean; Euclidean geometry, the classical pigeonhole principle, Banach contraction theory, and OpenAI Math #094's existential Lp embedding are included as written mathematical arguments. Literature priority remains unverified.

## The finite multibasin code theorem

Let \(I=\{1,\ldots,m\}\) index distinct attracting fixed points \(p_i\) of a single recurrent transition \(F\) in a real Hilbert space. For a chosen late time \(t\), assume a trajectory from basin \(i\) has state \(x_i(t)\) and a certified tail radius

\[
\|x_i(t)-p_i\|_2\le b_i(t).
\]

Let an encoder assign a finite terminal code \(c_i(t)\in \mathcal C\), with a reconstruction metric \(d_{\mathcal C}\), and suppose the additive distance distortion between every pair is at most \(E_t\):

\[
\left|\|x_i(t)-x_j(t)\|_2-d_{\mathcal C}(c_i(t),c_j(t))\right|\le E_t.
\]

**Theorem A (necessary attractor-label capacity).** If the attractor centers satisfy

\[
\|p_i-p_j\|_2 > b_i(t)+b_j(t)+E_t
\quad\text{for all }i\ne j,
\]

then the map \(i\mapsto c_i(t)\) is injective. Thus a code alphabet for such late histories must satisfy

\[
\boxed{|\mathcal C|\ge m,\qquad
\text{fixed-width tag bits}\ \ge\lceil\log_2 m\rceil.}
\]

**Proof.** If \(c_i(t)=c_j(t)\), the metric of the two identical codes is zero, hence \(\|x_i(t)-x_j(t)\|\le E_t\). The triangle inequality gives

\[
\|p_i-p_j\|
\le b_i(t)+\|x_i(t)-x_j(t)\|+b_j(t)
\le b_i(t)+E_t+b_j(t),
\]

contradicting the assumed strict separation. The code map is injective, and finite cardinality plus the pigeonhole principle imply the bit lower bound. \(\square\)

For a uniform pairwise attractor separation \(\Delta>0\), uniform tail bound \(b(t)\), and distortion budget \(E_t\), a sufficient gate is \(2b(t)+E_t<\Delta\). This makes the need for basin labels a directly measurable compression constraint. A tag is information about the asymptotic recurrent state, with no a priori semantic interpretation.

The new MathCan/BasinCodes.lean proves the generalized injectivity conclusion for arbitrary state, source-index and code types equipped with a natural-number distance triangle inequality. These assumptions stand in for the real-metric proof rather than claiming the real-valued theorem is Lean-formalized.

## An upper bound with separate anchors

Now assume each recurrent stream \(i\) has a certified entry into an invariant contraction ball and a tail radius bound \(b_i(T)\) for every time at least \(T\). Form the finite pooled set containing the \(m\) attractors and \(m\) observed trajectories of length \(T\), with at most \(m(T+1)\) points. Embed the real Euclidean space into real \(L_p\) by normalized Gaussian functionals, then apply OpenAI Math #094, *Subpolynomial dimension reduction in Lp*, at fixed \(1<p<\infty\), \(p\ne2\), \(D>1\).

The result is an existential finite embedding with coordinate bound

\[
d\le\exp\left(
C_{p,D}(\log(m(T+1)))^{\gamma(p)}
\right),
\]

where \(\gamma(p)=2-p\) for \(p<2\) and \(1-2/p\) for \(p>2\).

Represent each stream after time \(T\) by the image of its own fixed point. The triangle inequality bounds the error for any two observed or clipped times, including pairs crossing basins, by

\[
\boxed{E_T+2\max_i b_i(T)}
\]

where \(E_T\) is the maximum observed-pool additive distortion including all anchors. This bound includes a memory of each basin in the terminal codebook. It applies to genuine nonlinear post-entry trajectories, conditional on the individual capture certificates.

The lower bound on basin labels and this upper bound on finite history coordinates constrain different parts of the representation: the former requires that separated modes remain distinguishable, while the latter bounds the coordinates needed to approximate the entire finite prefix and its anchored tails. The existential #094 construction is not itself a trained compression algorithm.

## Application to the trained RRC-25 GRU

NOR-04/05 and NOR-07 independently certified two distinct period-one fixed points in the original 1,000-parameter trained real-analytic GRU. The centers of the certified balls are separated by more than \(1.8389154011509952\) using one coordinate alone.

NOR-06B provided an exact finite-entry witness for the signed-family public-input continuation into the first basin after 1,308 zero-input recurrent transitions. NOR-07 established a second attracting fixed point near the squared-family terminal FP64 candidate. A source-to-second-basin capture proof is still required to apply the all-time two-stream representation theorem to these two naturally sourced inputs.

The companion [NOR-08 second-basin radius survey](https://github.com/MoralityLabAI/Compactification-Theory/pull/150) seeks an enlarged rationally certified invariant ball around the second fixed point and measures first FP64 crossings from the original squared-family public features. Once a genuine source capture witness exists, the center-separation lower bound implies that any low-distortion late-history compactifier must retain at least a binary attractor label.

Mechanistic interpretability application: treat the attractor label as an observable feature of recurrent hidden-state dynamics. Its causal relevance to reasoning or reward behavior requires targeted interventions and held-out outcomes beyond the geometric certificate.
