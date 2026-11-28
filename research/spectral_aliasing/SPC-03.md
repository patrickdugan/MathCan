# SPC-03: DC masking, differential observability and damped phase schedules

**15 November 2026.** Independent extension of SPC-01 and SPC-02.

**Sources and scope.** The source pairing remains OpenAI Mathematics family #129,
*An exponential two-way deterministic state lower bound for one-way liveness*,
and family #130, *Finite tensor savings and exact Fourier circuits*, at
`openai/math@4eaee87548250b2682affda7d05d947c05554bae`. The former suggests
deferred-test state distinguishability; the latter motivates Fourier/tensor
coordinate analysis. None of the theorems below imports either source's
headline claim, and no automata lower bound or circuit improvement is claimed
for actual transformers. These elementary theorems are a new **combination for
this research program**, not a claim of first discovery of the ingredients.
See the exact URLs in [SPC-02](SPC-02.md).

## Theorem 1. Exact masking of centered recurrence by a stationary anchor

Let `x ∈ C^(T×D)` be a depth-by-channel activation trace. Write
`μ=(1/T)Σ_t x_t`, `z_t=x_t−μ`. Let `P` be the least-squares projector onto
`n`-periodic sequences over the observed window. Concretely, `(Px)_t` is
the mean over the observed depths congruent to `t mod n`. This `P` is an
orthogonal projection and preserves every constant-in-time trajectory.
Set `E=||x−Px||_F²`, `V=||z||_F²`, and `B=T||μ||²`.

The **exact DC-masking identity** is

\[
  ||x||_F^2=B+V,\quad ||(I-P)x||_F^2=||(I-P)z||_F^2=E,
\]
\[
 \boxed{r_{\rm raw}^2=(1-f_{\rm DC})r_{\rm centered}^2},\qquad
 f_{\rm DC}=B/(B+V),\quad
 r_{\rm raw}=\sqrt{E/(B+V)},\quad
 r_{\rm centered}=\sqrt{E/V}.
 \tag{1}
\]

**Proof.** `z` has temporal mean zero, so it is orthogonal to the
constant vector `1⊗μ`; Pythagoras yields `||x||²=B+V`. Since
`P(1⊗μ)=1⊗μ`, `(I−P)x=(I−P)z`. Substitute in the definitions. QED.

**Unbounded masking family.** For any fixed nonperiodic `z` with zero
mean and `E>0`, define `x^(a)_t=z_t+a v` for nonzero channel vector `v`.
The centered residual stays exactly constant for all real `a`, while
`r_raw(x^(a))→0` and `f_DC→1` as `|a|→∞`. Consequently, a raw small
periodic-fit error is compatible with arbitrary centered misspecification.
No spectrum or model architecture assumption is needed.

## Theorem 2. Affine contraction and its rounding floor

For `h_{t+1}=A h_t+b` in a normed finite-dimensional vector space, the
increment `Δh_t=h_{t+1}−h_t` obeys

\[
 \boxed{\Delta h_{t+1}=A\Delta h_t}.\tag{2}
\]

This follows by subtracting consecutive recurrence equations. When
`||A||≤κ<1`, differences obey `||Δh_t||≤κ^t||Δh_0||` and, writing
`h_*=(I−A)^{-1}b`, `||h_t−h_*||≤κ^t||h_0−h_*||`.

If `||h_*||>M:=||h_0−h_*||`, temporal centering and the minimizing
property of the mean give

\[
  \sum_{t<T}||h_t-\bar h||^2
    \le\sum_{t<T}||h_t-h_*||^2\le M^2/(1-κ^2),
\]
\[
 \boxed{1-f_{\rm DC}\le
 \frac{M^2}{T(1-κ^2)(||h_*||-M)^2}}.\tag{3}
\]

Here each `||h_t||≥||h_*||−M`, hence the squared total energy is at least
`T(||h_*||−M)^2`. So for a stable nonzero fixed point, **DC dominance
becomes inevitable as the observation window grows**, independently of
oscillatory Fourier sparsity. Formula (3) is one sufficient bound, not
an estimate of the Jacobian norm for a nonlinear model.

Now consider the noisy affine recurrence
`\tilde h_{t+1}=A\tilde h_t+b+e_t` with `||e_t||≤η`, initially
`\tilde h_0=h_0`. The state error satisfies

\[
 \boxed{||\tilde h_t-h_t||\le \eta(1-κ^t)/(1-κ)}.\tag{4}
\]

Indeed, the error recurrence is `d_{t+1}=A d_t+e_t`; take norms and
sum the geometric series. Successive observed differences inherit a
bound `2η/(1−κ)`. Once the true `||Δh_t||` is comparable to the
floating-point perturbation floor, fitting contraction from later
differences becomes ill-conditioned. Formula (4) is an **absolute
error** bound for an externally bounded-error recurrence. It is not a
rigorous characterization of PyTorch's rounding, whose per-step error
bound requires additional implementation analysis.

## Theorem 3. Differential Hankel rank for a finite transient spectrum

Suppose a complex scalar recurrence has the exact representation

\[
 h_t=c+\sum_{j=1}^{r} a_j\lambda_j^t,
 \quad a_j\ne0,\ \lambda_i\ne\lambda_j,\ \lambda_j\ne1.
\]

Its first differences are
`Δh_t=Σ_j a_j(λ_j−1)λ_j^t`, so for a Hankel matrix of `u` rows
and `v` columns with `u,v≥r`,

\[
 H_{s,t}=\Delta h_{s+t}=V_u\operatorname{diag}
 \bigl(a_j(\lambda_j-1)\bigr)V_v^T,
\]
\[
 \boxed{\operatorname{rank}H=r}.\tag{5}
\]

**Proof.** The factorization is direct. Both Vandermonde matrices have
full column rank because the poles are distinct. The middle diagonal
matrix is invertible. A left inverse for the first factor and a right
inverse for the last imply rank at least r; the factorization gives
rank at most r. QED.

The temporal anchor disappears and every pole receives a factor
`λ_j−1`. Higher-order differencing suppresses near-stationary poles by
`|λ_j−1|^m`; noise difference operators can amplify input noise by up
to `2^m` in Euclidean norm (operator-norm submultiplicativity and
`||shift−I||≤2`). Thus aggressive detrending can erase slow informative
modes, even when it corrects the DC-mask identity.

## Theorem 4. Exact delay scaling for damped Fourier phases

Fix `d≥2`, a damping factor `0<ρ≤1`, `ω=exp(2πi/d)`, and a phase schedule
`S={s_0,...,s_{q-1}}⊂{0,...,d−1}`. Consider an exact damped periodic-mode
family `x_t=Σ_{r=0}^{d−1} a_r (ρ ω^r)^t`. Measurements at loop depths
`L+s`, `s∈S`, have matrix

\[
 M_{L,S}(s,r)=\rho^{L+s}\omega^{(L+s)r}
 =\rho^L D_S V_S U_L,
\]

where `D_S=diag(ρ^s)`, `V_S(s,r)=ω^{sr}` and
`U_L=diag(ω^{Lr})` is unitary diagonal. For any support size `p≤q` let
`g_p(M)=min_{|J|=p}σ_min(M_{:,J})`. Right multiplication by `U_L`
rotates the columns without changing their singular values. Therefore

\[
 \boxed{g_p(M_{L,S})=\rho^L g_p(M_{0,S})}.\tag{6}
\]

Moreover, for `s_max=max S` and `s_min=min S`,

\[
 \rho^{L+s_{\max}}g_p(V_S)
 \le g_p(M_{L,S})
 \le\rho^{L+s_{\min}}g_p(V_S).\tag{7}
\]

This follows from `σ_min(D_SB)≥min_s ρ^s σ_min(B)` and the analogous
upper comparison using the smallest singular vector of `B`.
For `p=min(2k,d)` and a full-spark schedule, exact noiseless sparse
identifiability persists at every finite delay. Its *absolute stability
margin* shrinks by exactly `ρ^L`. At fixed measurement noise scale,
late observations eventually lose the ability to distinguish modes.

As an explicit two-hypothesis impossibility control, take two spectra
with different singleton supports and equal unit amplitudes. Their
measurement difference has norm at most `2√q ρ^{L+s_min}`. Adversarial
noise balls of radius `ε≥√q ρ^{L+s_min}` overlap at the midpoint.
No deterministic decoder can uniformly identify the true support at
that noise radius; this follows from two indistinguishable admissible
observations, rather than computational assumptions.

## Theorem 5. Early consecutive probes become optimal under strong damping

Take `q=p≤d`, and assume all `p`-column submatrices of `V_{S_0}` have
full rank for `S_0=(0,...,p−1)` (true for distinct Fourier roots by
the Vandermonde determinant). Let `g_0=g_p(V_{S_0})>0`.

The consecutive schedule has
`g_p(D_{S_0}V_{S_0})≥ρ^{p−1}g_0`.
Any different `p`-subset `S` of `{0,...,d−1}` has `s_max≥p`. Fix a
`p`-column support and a unit vector in the nullspace of its first
`p−1` rows. All but the final output coordinate vanish, and the
remaining row has norm at most `√p ρ^{s_max}`. Hence

\[
  \forall S\ne S_0,\quad g_p(D_SV_S)\le\sqrt p\,\rho^p.
\]

Therefore, for `0<ρ<g_0/√p`, the consecutive schedule is the
**unique strict minimax optimum** among all `p`-phase schedules:

\[
 \boxed{g_p(D_{S_0}V_{S_0})>
           \max_{S\ne S_0}g_p(D_SV_S)}.\tag{8}
\]

This theorem explains a qualitative reversal of the SPC-02 undamped
optimum. The sufficient range is conservative. It does not claim the
exact crossover for arbitrary dimensions.

## SPC-03 executable evidence

The applied code enumerates every phase schedule and every four-column
minor for `d=7`, `k=2`, `q=4`, with gain defined as above. For
`ρ≈0.43536`, fitted from native untrained `LoopedChase` first differences
as a **scalar local proxy**, the best damped schedule is `[0,1,2,3]`.
The undamped optimum `[0,1,2,4]` becomes inferior. A floating-point
bisection between 0.5 and 0.7 locates the crossover for this one pair
near `ρ=0.5881987013`. The native dynamics are nonlinear and
state-vector valued; the scalar estimate is not a measured eigenvalue
spectrum of their Jacobian. The phase-schedule theorem applies to the
**constructed damped Fourier model** only.

A 4-seed by 4-prompt untrained native control replays identical
float32-initialized weights and prompts at both float32 and float64.
It uses fixed early fit pairs (`delta` indices 3..8) and held-out pairs
(9..14). The float64 mean held-out AR(1) difference error is about
0.0745 times the observed held-out difference norm, against 1.0 for
the zero predictor and 1.236 for persistence. After loop 41, the
float64 state-change norm has fallen to roughly `10^-14`, versus the
float32 plateau near `10^-6`. Both are compatible with a contracting
transient and a float32 precision floor. They do **not** establish
that learning caused a fixed point, or a particular causal eigenmode.

## Formalization boundary

`MathCan/ContractionAliasing.lean` kernel-checks integer affine
increment identities, cancellation of static anchors, a two-coordinate
quadratic energy identity, and injectivity of one finite modulus-
11 affine transition. The Hilbert-space inequalities, complex Hankel
factorization and damped singular-value theorem have the explicit
mathematical proofs above. Machine formalization of those general
statements remains open. The companion Python tests exercise numerical
small cases and a trained-model-free native replay.

Next scientific validation must compare a trained checkpoint with a
matched untrained checkpoint, compute a state-space Jacobian or a
controlled perturbation, and evaluate task-level retention under
actual phase-selective interventions. These results remain diagnostic.
