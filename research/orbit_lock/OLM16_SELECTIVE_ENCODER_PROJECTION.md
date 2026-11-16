# OLM-16: Selective SAE erasure, tangent shams and task-margin geometry

November 16, 2026. Companion to the prospectively registered [SMC-16 protocol](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc16-selective-feature-kill-20261116/research/real_recurrence_sae_v1/SMC16_PROTOCOL.md). This note concerns a fixed affine SAE encoding cell. No neural computation or Lean verification follows from its rational regression tests.

## 0. Small-dimensional obstruction search before proof

The exact-rational oracle enumerates coordinate witnesses in dimensions 3 through 6, recording the rank and feasibility of the kill and sham constraints. At d=3, setting O to the three coordinate covectors and a equal to the first other-active covector makes the target unsuppressible while retaining those three. At d=4, with O=(e1,e2,e3) and a=e4, selective erasure exists but a nonzero sham preserving all four preactivations cannot exist: ker([O;a])={0}. At d=5, append e5: both edits exist and can have identical norm. In d=6, linearly dependent O rows remain a preregistered numerical abstention even though the mathematical projection can be defined using a pseudoinverse. See test_selective_projection.py for exact witnesses.

## 1. Unique minimum-norm feature kill

Fix a hidden state h in R^d. The originally active non-target encoder covectors form O in R^(3×d), assumed full row rank. The matched target covector is a, its clean positive top-four coefficient is z, and the specified overshoot is tau>0. The required physical subtraction delta satisfies

\[
 O\delta=0,\qquad a\delta=q:=z+\tau>0.
\]

Set

\[
 P=I-O^\top(OO^\top)^{-1}O,\qquad v=Pa.
\]

**Theorem OLM-16A.** If v=0, the joint constraints are infeasible. If v≠0, they admit the unique minimum-Euclidean-norm solution

\[
 \delta_*=\frac{q}{\|v\|^2}v,\qquad \|\delta_*\|=\frac{q}{\|v\|}.
\]

**Proof.** Every feasible delta lies in ker O, where a·delta=(Pa)·delta=v·delta. Cauchy–Schwarz gives q≤||v|| ||delta||. The displayed delta meets both constraints and achieves equality. Strict convexity of squared norm on the affine constraint set gives uniqueness. If v=0, a is in the row space of O and its value is fixed whenever O delta=0. QED.

The fixed SMC-16 norm cap is equivalently the test q/||v||≤6||z d_j|| for its native decoder column d_j. This identity is algebraic and leaves the physical norm scale fully exposed.

## 2. Tangent sham and cell stability

Let A be the four clean-active encoder covectors, including a. A sham displacement s with As=0 preserves all four affine preactivations exactly, for any displacement amplitude. A nonzero such sham exists exactly when rank(A)<d. For d=48 and rank(A)≤4 this linear nullspace is large; a nonzero random seed can still project to zero and must be rejected.

**Theorem OLM-16B (strict top-four support test).** Suppose the clean selected four preactivations are strictly positive. For a physical subtraction s in ker A, those four remain the strict top four if, for each inactive feature l, its changed affine preactivation b_l−a_l·s is strictly below the minimum of the four clean active preactivations. This is necessary and sufficient for strict ordering at the new state. The lower-dimensional exact witness with A=(e1,e2,e3,e4), inactive a5=e5 and clean b5=−1 has s=−3e5 in ker A, yet its changed inactive preactivation becomes 2 and overtakes active preactivations equal to 1.

For the selective target kill, exact preservation of the other three *affine* preactivations does not by itself guarantee their post-reencoding top-four membership. The registered experiment accordingly checks actual SAE reencoding for both arms and rejects contaminated cases before inspecting any output digit or margin.

## 3. Task-margin sensitivity and a sharp curvature remainder

Let m be the frozen continuation's ground-truth digit-minus-fixed-clean-rival margin. Compare a selective kill delta_* with a tangent sham s of equal Euclidean norm r. Put

\[
 D=m(h-s)-m(h-\delta_*).
\]

**Theorem OLM-16C.** If m is twice continuously differentiable over both closed intervention segments and ||D²m(x)||op≤M on them, then

\[
 \left|D-\nabla m(h)\cdot(\delta_*-s)\right|\le Mr^2.
\]

In particular, \(\nabla m(h)\cdot(\delta_*-s)>Mr^2\) is sufficient for D>0. The Mr² constant is sharp under independent Hessian bounds on the two segments.

**Proof.** Taylor's integral remainder gives m(h−u)=m(h)−∇m(h)·u+R(u) with |R(u)|≤M||u||²/2. Subtraction yields the stated inequality. For sharpness, take h=0, delta_*=r e4, s=r e5 and m(x)=(M/2)(x4²−x5²): D=−Mr² while the linear term is zero. QED.

Equal dose controls the remainder; the directional first-order term still determines the sign in the small-radius regime. This bound is an exact-real statement. The SMC-16 measured margins use FP64 recurrence without interval-arithmetic certification.

## 4. Exact nonidentifiability even after perfect selective editing

**Theorem OLM-16D.** Identical clean SAE codes, identical top-four support, an exact kill, an exactly tangent equal-norm sham, and agreement on all clean task classifications are insufficient to identify the sign of D.

**Proof by dimension-five witness.** Let O=(e1,e2,e3), a=e4, h=(1,1,1,1,0), z=1, tau=1/4. Then delta_*=(5/4)e4 and s=(5/4)e5 satisfy the constraints, with equal physical norm. Choose two margins

\[
 m_+(x)=3+x_4-x_5,\qquad m_-(x)=3-x_4+x_5.
\]

Both clean margins are positive (4 and 2), and all SAE codes are the same because the encoders are shared. Yet D_+=5/2 and D_-=-5/2. Their Hessians vanish, so curvature control alone cannot fix the sign. QED.

## 5. Inactive encoder leakage

For any other feature covector b, the change in affine preactivation from the optimal target kill is

\[
 b\delta_*=\frac{q}{\|v\|^2}(Pb)\cdot v,
 \qquad |b\delta_*|\le \frac{q\|Pb\|}{\|v\|}.
\]

**Theorem OLM-16E.** The upper bound is sharp, with equality whenever Pb is proportional to v with the relevant sign. This is an exact certificate for how much an initially inactive encoder row may move under an otherwise perfectly selective active-row kill. There is no corresponding guarantee that inactive rows are unchanged.

## Validation and formalization boundary

The stdlib-only Fraction oracle tests exact minimum norm, feasibility and rank boundaries, fixed-cell support, the sharp quadratic remainder, the two-teacher sign reversal, and inactive-row leakage. Unit tests are independent of all model checkpoints. The proofs use elementary finite-dimensional linear algebra and Taylor's theorem. **Lean scope:** OLM-16A, B and E admit rational matrix verification and real inner-product formulations; OLM-16C needs real C² calculus; OLM-16D is a dimension-five explicit algebraic witness. Lean formal proofs remain future work. The trained-network causal evidence must be evaluated separately in the source-pinned SMC-16 experiment.
