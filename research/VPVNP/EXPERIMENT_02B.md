# VPVNP-02B: spectral proof decomposition and a stability bound

Registered 2026-11-24. VPVNP-01 and VPVNP-02A independently passed [MathCan CI](https://github.com/patrickdugan/MathCan/actions/runs/45319719088), including the full pinned upstream native and nanoda replay.

RankSpectral.lean contains a proposed native Lean proof of the finite orthogonal expansion, shift energy, mixture inequality, and conditional sharp bound. The hypotheses of orthogonality and reconstruction are explicit. Actual binary-matrix Walsh orthogonality, reconstruction, GL rank counts, and the finite q-binomial/Mobius identities remain VPVNP-02C obligations. The upstream verified theorem and this proposed new formalization are separate.

## New analytic extension: stability of the extremizer

Put q=2^n and C=2(1-1/q). Write p_r(k) for the rank-r parity probability on dual rank k, and let e_B=||h_B||^2 be nonnegative Walsh energies. Set w_B=e_B p_1(rank B). Exclude the constant mode B=0. For k>=2, z=2^(n-k)<=q/4 gives p_1(k)>=3/2 p_1(1), whereas p_n(k)<=p_n(1). Consequently p_n(k)/p_1(k)<=2C/3 for k>=2, and the exact rank-one ratio is C. Define eta=sum_{rank B>=2}w_B / sum_{B!=0}w_B when the denominator is positive. Then

    R = D_f(n)^2 / D_f(1)^2 <= C (1-eta/3).

In particular R>=C(1-epsilon) implies eta<=3 epsilon. This is a one-sided concentration certificate for the **rank-one denominator-weighted spectral energy**, not for unweighted energies, parameter count, or task correctness. It holds for the registered binary rank strata if the character formulas and Walsh representation hold. If R is small, it does not imply high-rank content; contraction alone is automatic for this observer class.

## Preregistered verification

B1: unnormalized scalar Parseval given orthogonal finite characters; shift energy under multiplicativity and exact reconstruction. Vector extension by summing coordinates is elementary but is not claimed as a Lean declaration here.
B2: nonnegative weighted ratio, explicit singleton equality and weighted defect inequality.
B3: conditional componentwise rank floor, upper ceiling, sharp constant, gap for k>=2 and rank-one attainment for real q>1.
B4: exhaustively test the relative gap at n=2,3,4 from the registered archived results; deterministic mixtures include all single modes, fixed integer-weight mixtures, a constant/undefined case, and near-saturation examples. Use Fraction; no tuning. Acceptance requires zero violations and a new native kernel log listing only the standard axioms for all named targets. Do not label B1-B3 verified before the kernel log.

The next step (02C) builds the actual matrix Walsh basis and proves the exact character-sum formulas, with no additional mathematical axioms. It must then compose them with 02B before advertising a complete Lean theorem for all binary matrices.
