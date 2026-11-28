# SPC-03J: Jacobian secant error and what a local eigenvalue establishes

**15 November 2026.** Mathematical supplement to
[SPC-03](SPC-03.md), motivated by the LoopedTransformers native
full-state Jacobian experiment. The source papers remain the paired
OpenAI Mathematics families #129 and #130 described in SPC-02.

## Theorem: endpoint-Jacobian quadratic secant error

Let `F: U→R^N` be continuously differentiable on an open convex set
containing the segment joining `x` and `y`. Assume the Jacobian is
operator-Lipschitz along this segment:

\[
 ||J_F(u)-J_F(v)||_{op}\le L||u-v||_2.
\]

Then, with `d=y−x`,

\[
 \boxed{||F(y)-F(x)-J_F(y)d||_2\le (L/2)||d||_2^2.}
 \tag{1}
\]

**Proof.** The vector fundamental theorem of calculus gives
`F(y)-F(x)=∫_0^1 J_F(x+td)d dt`.
Subtract `J_F(y)d` under the integral. By Lipschitzness,
`||J_F(x+td)-J_F(y)||≤L(1-t)||d||`.
Use the triangle inequality for integrals and evaluate
`∫_0^1(1−t)dt=1/2`. QED.

For a recurrent trajectory `h_{t+1}=F(h_t)`, write
`d_t=h_{t+1}−h_t`. Since `d_{t+1}=F(h_{t+1})−F(h_t)`, (1) becomes

\[
 \boxed{||d_{t+1}-J_F(h_{t+1})d_t||\le (L/2)||d_t||^2.}
 \tag{2}
\]

This is a direct **finite-trajectory Jacobian audit**: relative
prediction error should tend toward zero with the contraction,
provided `||d_{t+1}||` stays above the numerical precision floor.
The theorem applies to nonlinear recurrent maps and all token-state
coordinates, regardless of any Fourier sparsity assumption.

## Sharp polynomial witness

For the scalar quadratic map `F(x)=a x²+b x+c` over the reals,
`J_F(y)=2ay+b` and the exact remainder is

\[
 \boxed{F(y)-F(x)-J_F(y)(y-x)=-a(y-x)^2.}\tag{3}
\]

To verify, expand the difference `a(y²−x²)+b(y−x)` and subtract
`(2ay+b)(y−x)`. The surviving polynomial is `−a(y−x)²`.
Here `L=2|a|`, so the bound (1) is attained with equality.
This shows that the coefficient `1/2` in the general bound is sharp.

`MathCan/JacobianSecant.lean` checks (3) modulo seven for all 2,401
choices of `(a,b,x,y)`, using the exact finite-field derivative.
The general `C¹,¹` theorem and operator norms remain paper proofs.

## Eigenvalues, nonnormality and observable decay

If `h_*` is a fixed point and `J_*=J_F(h_*)` has eigenvalues inside the
unit disk, the **linearized** dynamics have spectral radius below one.
For a diagonalizable `J_*=VΛV^{-1}`,

\[
 ||J_*^t||_2\le \kappa_2(V)\rho(J_*)^t.
 \tag{4}
\]

**Proof.** Use `J_*^t=VΛ^tV^{-1}` and submultiplicativity. QED.

The prefactor `κ₂(V)` matters: a nonnormal recurrence can amplify
some directions transiently even with spectral radius below one.
A scalar AR(1) coefficient fitted to an observed answer-position
increment is a Rayleigh-like projection on the visited trajectory,
so it need not equal any individual eigenvalue.

For a normal `J_*`, a nonzero vector `v` and scalar `a` obey the
residual-to-spectrum bound

\[
 \boxed{\min_{\lambda\in\sigma(J_*)}|a-\lambda|
     \le ||J_*v-a v||_2/||v||_2.}\tag{5}
\]

**Proof.** Unitarily diagonalize `J_*` and expand the squared norm
as a weighted sum of `|λ_j−a|²`. The minimum is bounded by the
weighted mean. QED. For nonnormal matrices the eigenvector basis
condition number enters analogous bounds.

## Native audit

On four untrained LoopedChase seeds, the full-state `F_e` (nine tokens,
64 channels each) was reconstructed from the actual model modules and
matched `model.forward` exactly. A float64 Arnoldi calculation of four
leading eigenvalues of the terminal full-state Jacobian gave largest
moduli `0.46553, 0.45702, 0.47014, 0.46975`, mean `0.46561`.
The observed mean endpoint-Jacobian secant relative error at
difference index 12 was `4.47e−7`, versus around `2.4e−4` at index 4
in the representative first seed. This measured decrease is
consistent with (2), and a complete proof of the bound for the
specific network would require a certified local Jacobian Lipschitz
constant and a numerical precision audit.

The exact-full-state test matters: the Jacobian on the answer token
alone ignores the recurrent influence from prompt-token states.
Future trained-vs-untrained comparisons should use the **same** full
state-space definition, matching input sequences and independent
random seeds before interpreting the spectrum as a learned mechanism.
