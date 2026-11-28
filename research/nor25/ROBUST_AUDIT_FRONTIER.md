# NOR-25: the robust uniform-reserve audit frontier

Companion mathematics to [Compactification-Theory NOR-25](https://github.com/MoralityLabAI/Compactification-Theory/pull/193), extending MathCan's NOR-23 exact finite audit counts and NOR-24 sequential transcript indistinguishability.

## Finite theorem

Consider an output of m indexed coordinates, a deterministic publicly chosen targeted-risk prefix T of size t and an independent random reserve R of size u sampled uniformly among the m-t coordinates outside T. The attack set A has exactly r distinct coordinates and is fixed before drawing R. The audit checks T union R and rejects on any authentic exact mismatch.

If A intersects T, every audit detects it. If A avoids T, the number of possible R without an altered coordinate is C(m-t-r,u), and there are C(m-t,u) equiprobable possible R. Therefore the exact fixed-blind miss probability is

    C(m-t-r,u)/C(m-t,u),

with detection

    1 - C(m-t-r,u)/C(m-t,u).

Provided r<=m-t and u<=m-t, an attacker whose choice precedes the audit randomness can attain the upper miss probability by avoiding T. This establishes the exact *minimax detection floor* over all fixed radius-r attacks, for any possible targeted selector.

The Lean proof file [NOR25UniformReserve.lean](../../MathCan/NOR25UniformReserve.lean) encodes residual changed-coordinate masks. It proves the two-stage missed/total count pair, the bound on misses when the prefix already detects an attack, and preservation of exact rejection after adding any reserve. The theorem for a schedule-informed adversary constructs a distinct hidden target with the same full witnessed transcript whenever an unchecked coordinate exists.

## Reserve-fraction frontier

For a fixed total k, set u=k-t. If m-k>=r>0, survival at the adversarial worst case is

    Q(u) = C(m-k+u-r,u)/C(m-k+u,u).

The factorial ratio telescopes:

    Q(u) = PRODUCT_(j=1)^u (m-k+j-r)/(m-k+j).

Thus Q(0)=1, Q(u+1)/Q(u)=(m-k+u+1-r)/(m-k+u+1)<1, and the minimax detection floor 1-Q(u) strictly increases with reserve size u. The strict improvement costs targeted inspections, which is why the measured in-template rate belongs to the separate prospective NOR-25 experiment.

For the registered k=16, r=4, u=8, the exact floor is

    1 - C(m-12,8)/C(m-8,8),

at m=769 and 1537. Every policy constrained to a fixed risk prefix and an independent uniform reserve shares this lower bound, regardless of learned risk scores.

## Threat-model boundary

The guarantee quantifies over a fixed attack A chosen before the random reserve. Publicly releasing the realized sampled set changes the game: the adversary can choose a changed coordinate outside all checked positions and preserve the entire ordered exact-value transcript. The MathCan theorem makes this distinction explicit.

This pure finite counting result assumes an honest exact-value oracle. It certifies a mathematical audit allocation property, not real-world randomness secrecy or a sound full-output proof system. The corresponding prospective empirical readouts and challenge construction are controlled by the precommitted Compactification-Theory registration.
