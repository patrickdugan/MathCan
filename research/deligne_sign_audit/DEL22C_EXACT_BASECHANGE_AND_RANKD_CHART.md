# DEL-22C: exact ideal specialization and arbitrary-rank pivot charts

## Exact universal-to-fixed incidence base change

Over a field K, let P=K[a_i,c], S=P[z_i], and T=K[z_i].
Let phi:S -> T fix K and specialize the independent parameter coefficients.

DEL-22B established that every original generator, section polynomial,
and augmented Jacobian minor is carried to the corresponding
fixed-parameter generator. Since their index families are unchanged,
the ideal-map/span lemma proves equality for their generated ideals:

\[
\begin{aligned}
\phi_*(I_{U^k}S)&=I_{U^k},\\
\phi_*((s))&=(s_{a,c}),\\
\phi_*(I_{d+1}([J;ds]))&=I_{d+1}([J;ds_{a,c}]),\\
\phi_*(J_d^{\mathrm{univ}})&=
I_{U^k}+(s_{a,c})+I_{d+1}([J;ds_{a,c}]).
\end{aligned}
\]

Four Lean declarations in RelativeCriticalBaseChange.lean formalize these
identities using Ideal.map_span and Ideal.map_sup. They preserve the
literal DEL-16 ideal and all redundant or nilpotent generators.
The branch requires a pinned Lean 4.35 kernel and axiom audit before
any result is reported as verified. The equality concerns the
*image/extended ideal*, not the inverse image under phi, which
usually contains the parameter specialization kernel.

## Arbitrary-rank chart: determinant and adjugate route

Let A be the original Jacobian at an L-valued point, and suppose its
row rank is d. Select d genuine original rows R and d source columns C
with invertible H=A[R,C] and Delta=det(H). Write g=ds.

For each source coordinate j define

\[
q_j=\Delta\,g_j-g_C\,\operatorname{adj}(H)A_{R,j}
   =\det\begin{pmatrix}H&A_{R,j}\\g_C&g_j\end{pmatrix}.
\]

The interpolation multiplier is lambda=g_C H^{-1}. Since rows R span
the actual original conormal space, g is conormal iff every q_j is
zero. In rank 1 this recovers DEL-22B's verified pivot chart. In rank
0 the requirement reduces to the vanishing of each coordinate of g.

Over the localized coordinate ring at Delta, block Gaussian
elimination yields the scheme-level determinantal identity

\[
I_{d+1}([J;g])=I_{d+1}(J)+(q_j:j).
\]

On an explicitly constant-rank-d chart the original higher minors
vanish *in the localized ring*, so q_j alone generates the
critical-rank drop condition. Pointwise rank arguments over residue
fields do not establish this scheme-level vanishing in a nonreduced ring.

When d<n, the augmented Jacobian is the actual finite presentation
matrix for the differentials of the section quotient.
Its size-(d+1) minor ideal is the standard
Fitt_{n-d-1} ideal of the corresponding Kahler module.
Kernel formalization of this presentation and its localization remains
a separate step.

## Remaining gates

1. The four ideal-image identities need the pinned Lean kernel,
   full Deligne04 import, expected axiom audit and arithmetic regression.
2. General rank-d chart needs the block determinant identity,
   constant-rank/localization hypotheses, and original-ideal transport.
3. L-valued coefficient specialization, elimination/projection
   closure and Katz weak Lefschetz remain unproved.

References: DEL-22B PR #256, DEL-22A PR #252, issue #253, parent #191.
