# SPC-01: phase-sparsu Fourier observability and recurrent state cost

**Date:** 2026-11-15. **Status:** new finite-dimensional mathematical synthesis with exact finite-field certificates. The complex-field arguments below are supplied explicitly; the Lean file checks a four-phase finite-field specialization, not the unrestricted theorem. Independent mathematical priority has not been established.

## Source pair

* OpenAI Math family **129**, *An exponential two-way deterministic state lower bound for one-way liveness* (September 25, 2026), [manuscript and source](https://github.com/openai/math/tree/main/preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026). The source proves its state-cost result for binary-relation words over alphabets growing with the number of relation points. Its specific exponential lower bound is **not** imported into this work.
* OpenAI Math family **130**, *Finite tensor savings and exact Fourier circuits* (September 25, 2026), [manuscript and source](https://github.com/openai/math/tree/main/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026). This source motivates exact Fourier coordinate changes. Its nonuniform arithmetic-complexity improvement is **not** imported into this work.

The new object is the **phase-observability transform** for recurrent outputs, with exact rank and a sharp identifiability threshold for unknown Fourier support. State cost here means minimal **complex-linear recurrent state dimension**, a different complexity measure from the source paper's two-way automaton state count.

## Setup and Fourier aliasing identity

Take positive integers \(m,d\), let \(n=md\), \(\omega=e^{2\pi i/n}\), and let \(x:\mathbb Z_n\to\mathbb C\) be a periodic scalar output of a recurrent dynamical system. Define

\[
\widehat x(f)=\sum_{t=0}^{n-1}x(t)\omega^{-ft},\qquad
x(t)=\frac1n\sum_{f=0}^{n-1}\widehat x(f)\omega^{ft}.
\]

A stride-\(d\) observation at phase \(s\in\{0,\dots,d-1\}\) is \(y_s(k)=x(s+dk)\) for \(k\in\mathbb Z_m\). Its \(m\)-point transform satisfies

\[
\boxed{\widehat y_s(j)=\frac1d\sum_{r=0}^{d-1}
\omega^{(j+rm)s}\widehat x(j+rm),\qquad 0\le j<m.}\tag{1}
\]

**Proof.** Substitute the inverse \(n\)-point transform into the definition of \(\widehat y_s(j)\), interchange the finite sums, and use \(\sum_{k=0}^{m-1}\exp(2\pi i (f-j)k/m)=m\) if \(f\equiv j\pmod m\) and zero otherwise. The factor is \(m/n=1/d\).

## Theorem A: exact phase-rank and blind dimension

For any set \(S\subseteq\mathbb Z_d\) of \(r\) distinct phases, the linear observation operator \(P_S:\mathbb C^n\to (\mathbb C^m)^r\), \(x\mapsto(y_s)_{s\in S}\), has

\[
\boxed{\operatorname{rank} P_S=mr,\qquad \dim\ker P_S=m(d-r).}\tag{2}
\]

**Proof.** The coordinate selection maps \(x(s+dk)\) for distinct pairs \((s,k)\) onto \(mr\) different canonical coordinates; the corresponding matrix rows are linearly independent. Equation (1) supplies an equivalent Fourier proof. After an \(m\)-point DFT on each output and a permutation of input Fourier coordinates, each residue class \(j\) has measurement matrix

\[
B_{S,j}(s,r')=d^{-1}\omega^{js}\zeta_d^{sr'},\quad
\zeta_d=e^{2\pi i/d},\quad s\in S,\ 0\le r'<d.
\]

The rows indexed by distinct \(s\) are pairwise orthogonal since \(\sum_{r'=0}^{d-1}\zeta_d^{(s-s')r'}=d\,\mathbf1_{s=s'}\). Each of the \(m\) blocks has rank \(r\), proving (2).

**Sharp blindness witness.** If \(S\ne\mathbb Z_d\), choose a missing phase \(s_*\) and let \(x(t)=\mathbf1_{t=s_*}\). All \(n\) Fourier coefficients of this period-\(n\) impulse are nonzero. Hence the full signal has maximal complex-linear recurrent order \(n\), but all observed sequences are identically zero. The measurement rank formula does not assume sparsity.

## Theorem B: sharp phase budget for unknown sparse alias classes

Suppose each alias class \(\{j+rm:0\le r<d\}\), \(0\le j<m\), contains at most \(k\) nonzero coefficients of \(\widehat x\), where \(1\le k\le d\). Select consecutive probe phases \(S_q=\{0,1,\ldots,q-1\}\). Then every such signal is uniquely identifiable from its observed periodic sequences if and only if

\[
\boxed{q\ge\min(2k,d).}\tag{3}
\]

**Proof of sufficiency.** Fix an alias class \(j\). Remove the known factors in (1):

\[
b_s=d\,\omega^{-js}\widehat y_s(j)
=\sum_{r=0}^{d-1}a_r\zeta_d^{sr},\qquad a_r=\widehat x(j+rm).
\]

The \(q\times d\) matrix \(V_{s,r}=\zeta_d^{sr}\), with \(s=0,\dots,q-1\), has every collection of up to \(q\) columns linearly independent. Indeed, its first \(\ell\) rows on any \(\ell\) selected columns form a Vandermonde matrix on pairwise distinct points \(\zeta_d^r\), with determinant \(\prod_{a<b}(\zeta_d^{r_b}-\zeta_d^{r_a})\ne0\). If two \(k\)-sparsu coefficient vectors produce the same \(b_s\), their difference is supported on at most \(2k\) columns. For \(q\ge\min(2k,d)\), the difference must vanish (when \(q=d\), the full Fourier matrix is invertible). Apply independently to every \(j\), then invert the length-\(n\) DFT.

**Proof of necessity.** If \(q<\min(2k,d)\), choose any \(q+1\) columns of \(V\). There is a nonzero dependence involving exactly these \(q+1\) columns, since every subset of size \(q\) is independent. The support size \(q+1\) is at most \(2k\). Partition those columns into two sets of size at most \(k\). Split the dependence into two distinct \(k\)-sparsu vectors with the same measurement. Insert thesu vectors into a single residue class and set all other classes to zero. This yields two distinct length-\(n\) signals with identical phase observations. When \(q=0\) the claim is immediate.

This theorem is an exact noiseless uniqueness statement over \(\mathbb C\). Computationally efficient recovery, stability under noise, and identification of unknown approximate sparsity remain separate questions. The provided sparsu decoder uses exhaustive support enumeration; it is deliberately restricted to small \(d\).

## Theorem B.2: sharp detection versus identification thresholds

Under Theorem B's assumptions, let \(k\le d\) bound the nonzero modes per alias class and use the first \(q\) phases. **Every occupied alias class is detectable** (i.e., some phase output has a nonzero Fourier coefficient at that residue) if and only if

\[\boxed{q\ge k}.\tag{3a}\]

**Proof.** A nonzero \(k\)-sparsu vector in an alias block cannot belong to the nullspace of the first \(q\) Fourier rows when \(q\ge k\), because every collection of at most \(q\) columns is independent. If \(q<k\), take a dependence among \(q+1\) columns, giving an invisible nonzero signal supported on at most \(k\) frequencies. This is an existence claim about a whole block, rather than individual frequency recovery.

Let \(B\) be the number of occupied alias classes. Whenever \(q\ge k\), the observed jointly periodic signal has exactly \(B\) active output frequencies, hence by Theorem C its observable linear state order is \(B\). If the full signal has \(R\) active Fourier modes, then

\[\boxed{B\le R\le k B,\qquad \operatorname{rank}H_{\mathrm{obs}}=B.}\tag{3b}\]

Combining this detection bound with Theorem B reveals a sharp intermediate regime \(k\le q<\min(2k,d)\): every occupied spectral alias class is observable, but different sparsu frequency assignments can produce identical observations. This is a precise distinction between detectable state activity and identifiable internal state structure.

**Phase arithmetic matters.** For phases \(s_t=s_0+a t\pmod d\), the same sharp thresholds hold when \(\gcd(a,d)=1\). Indeed, \(\zeta_d^{a r}\) are distinct roots, so the Vandermonde argument applies after removing the phase factor \(\zeta_d^{s_0r}\). If \(g=\gcd(a,d)>1\), columns for frequencies \(r\) and \(r+d/g\) are proportional for every chosen phase. Even one-sparsu frequency identification is therefore impossible under that schedule.

## Theorem C: periodic multi-output Hankel rank

Let \(Y:\mathbb Z_m\to\mathbb C^r\) be a jointly periodic observed signal. Form the block Hankel matrix \(H\in\mathbb C^{mr\times m}\) by \(H_{(s,i),j}=Y_s(i+j\bmod m)\). Then

\[
\boxed{\operatorname{rank}H=
\#\{f\in\mathbb Z_m:\widehat Y(f)\ne 0\}.}\tag{4}
\]

Moreover, the right side is exactly the minimal state dimension of a complex-linear time-invariant recurrent realization \(z_{t+1}=Az_t,\ Y(t)=Cz_t\) producing the entire periodic signal.

**Proof.** Fourier-expand \(Y(t)=\sum_f v_f\lambda_f^t\), with \(\lambda_f=e^{2\pi if/m}\) and \(v_f=m^{-1}\widehat Y(f)\). The Hankel matrix factors into columns \([v_f,\lambda_f v_f,\ldots,\lambda_f^{m-1}v_f]^\top\) and rows \([1,\lambda_f,\ldots,\lambda_f^{m-1}]\). The rows are independent by the invertible DFT. The left columns with \(v_f\ne0\) are independent: a Fourier transform along the block-row index isolates each \(v_f\) into its own coordinate. Thus the rank is the active-frequency count. Any \(r_0\)-dimensional linear recurrence factors its Hankel matrix through its state space, so \(r_0\ge\operatorname{rank}H\). Conversely, taking \(A=\operatorname{diag}(\lambda_f)\), initial state all ones, and output columns \(v_f\) for active modes realizes the signal in exactly that dimension.

For partially sampled loop activations, (4) measures **apparent** recurrent state cost; Theorem A describes the missing state space. The full-state impulse witness shows that unobserved phase classes can erase all evidence of a maximal-order recurrent mode.

## Exact certificates and experiment

* `MathCan/SpectralAliasing.lean` proves modulo 5 that \(2\) is a primitive fourth root; four-phase character sums are orthogonal, two consecutive phase probes distinguish all nonzero **one-sparsu** length-four frequency vectors, and explicit **two-sparsu** sources share the first three pilot values while the fourth separates them. These are finite specializations of Theorem B, without any Lean axiom or admitted proof.
* `tests/test_spectral_aliasing.py` checks the full-spark minors over \(\mathbb F_5\), enumerates all 625 four-coefficient vectors, and tests the three-phase collision. These are independent arithmetic oracles, not proofs of the complex-field generalization.
* `MoralityLabAI/LoopedTransformers/experiments/spectral_state_cost_v0` contains a no-dependency CPU gym for (1)–(4), with a small brute-force unknown-support Fourier decoder and a deliberately hidden high-order recurrence witness.

**Falsifiable next step:** measure depth-indexed activation trajectories of a looped model under full per-step observation, compute their periodic residual Hankel ranks, and repeat with phase-strided acquisition. Compare predicted alias cancellations with actual reconstruction error and out-of-distribution extrapolation. Real network trajectories will generally be approximately periodic, so departures from exact identities must be reported separately as approximation/model error.
