# NRF-07: finite-depth Jordan leakage scaling and independent-seed transfer

Date: 2026-11-15. Research-program mathematical derivation and exact finite oracle. Global novelty is **not claimed**: powers of Jordan blocks, classical observability, and balanced model reduction predate this work.

## Theorem: nilpotent depth law

For the two-dimensional nonnormal matrix J=aI+bN with N=E12 and N^2=0, direct binomial expansion gives

\[
J^R=a^RI+R\,a^{R-1}bN,\qquad R\ge1.
\]

For zero-mean isotropic input, task y=e1^T x, and rank-one orthogonal observation P=uu^T with u=(cos θ,sin θ), the optimal linear task prediction from Px has squared error E=sin²θ. The global linear dark-to-observed leakage after R tied iterations is

\[
L_R(P)=\|P J^R(I-P)\|_F
      =R |a|^{R-1}|b|(1-E).
\]

**Proof.** Since N²=0, every binomial summand beyond first order vanishes. Let v=(-sin θ,cos θ) span ker P. Then u^T J^R v=R a^{R-1}b cos²θ. The rank-one cross-fiber operator is this scalar times uv^T, giving the norm above. The projection risk is E=1-|\langle e1,u\rangle|².

For nonnegative λ, define task plus squared-leakage loss

\[
\mathcal J_R(E)=E+\lambda R^2|a|^{2R-2}b^2(1-E)^2,\quad 0\le E\le1.
\]

The exact minimizer is

\[
E^*=\begin{cases}
0 & 2\lambda R^2 |a|^{2R-2}b^2\le1,\\
1-\bigl(2\lambda R^2|a|^{2R-2}b^2\bigr)^{-1}&\text{otherwise}.
\end{cases}
\]

It follows by differentiation of a convex quadratic. A task-favoring projector with error E_A strictly below E_B crosses the competing projector at

\[
\boxed{\lambda_*(R)=
\frac{1}{R^2 |a|^{2R-2}b^2(2-E_A-E_B)}}.
\]

**Proof.** Write the equality of both objectives and cancel E_B-E_A>0 using
(1-E_A)²-(1-E_B)²=(E_B-E_A)(2-E_A-E_B). Positive b and a factors give the claimed finite threshold; if the shear after R steps vanishes, there is no finite crossover.

For the unipotent case a=1, doubling depth obeys

\[
\lambda_*(2R)=\lambda_*(R)/4.
\]

This is an exact depth law for a single Jordan block and two *fixed* observation projections. In the trained nonlinear 128D tied-loop experiments, the observed effective depth dependence is much steeper, so this simple mechanism alone does not account for the results. The learned projections also change with depth and training, and the leakage is sampled on a task distribution.

## Exact formal and arithmetic scope

- research/compactification/jordan_depth_frontier.py tests the analytic formulas with arbitrary Fraction coefficients, exact 2x2 products and optimal risk crossover calculations.
- tests/test_jordan_depth_frontier.py checks 273 independent matrix powers, 810 rank-one projector leakage identities, 30 exact crossover thresholds, and a rational minimizer grid.
- MathCan/JordanDepth.lean checks the **unipotent Nat recurrence** for powers of [[1,b],[0,1]] and the fourfold squared-depth factor; its Lean proof does not formalize the real stochastic task risk or differentiability.

## Applied replication

MoralityLabAI/LoopedTransformers PR #56 now includes the precommitted NRF-07 experiment, which trains newly initialized tied residual loops at depths 16 and 32 using task seeds 109, 113 and 127. With the previously selected λ=1, six final new checkpoints reproduce NRF-06's directional split: supervised decoder wins at R16, and the median random control wins at R32. The source model family and task remain synthetic; the new training seeds provide additional within-family replication.

Relevant related work includes Padovan (2026), *Non-Intrusive Balancing for Data-Driven Model Reduction with Oblique Projections*, https://arxiv.org/abs/2610.15219, and Kazma and Taha (2026), *Observability for Nonlinear Systems: Connecting Variational Dynamics, Lyapunov Exponents, and Empirical Gramians*, DOI: 10.1109/TCNS.2026.3721959. Those studies address observability/model reduction at broader scale. The explicit Jordan loss/leakage formula here is a program-specific specialization.
