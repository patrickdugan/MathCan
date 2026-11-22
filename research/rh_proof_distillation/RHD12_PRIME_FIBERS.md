# RHD-12: finite residue fibers for the actual HeightOneSpectrum bridge

**Source-pinned mathematical target:** leanprover-community/riemann-hypothesis commit f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3. **Parent arithmetic:** RHD-09/RHD-10, E = Q(zeta_20), ell = 29. **Kernel scope:** an Init-only finite-ring calculation, not actual number-field ideals.

## What is now proved in Lean

The new standalone module MathCan/RHPrimeFibers.lean defines multiplication on ordered integer remainder pairs modulo 29 with the quadratic relation alpha^2+c alpha-1=0. The quadratic factors have c = 2, 14, -14, -2, respectively.

A closed finite-search theorem proves none of those four quadratics has a root in F_29. Since each has degree two, this is the residue-field irreducibility certificate. A separate kernel computation evaluates alpha^5 in each quadratic residue ring:

| factor j | polynomial modulo 29 | alpha^5 | proposed Q(i) contraction |
| --- | --- | --- | --- |
| 0 | X^2+2X-1 | 17 | root 17 of X^2+1 |
| 1 | X^2+14X-1 | 12 | root 12 of X^2+1 |
| 2 | X^2-14X-1 | 17 | root 17 of X^2+1 |
| 3 | X^2-2X-1 | 12 | root 12 of X^2+1 |

Both 17^2+1 and 12^2+1 vanish modulo 29, while 17 and 12 differ. The two distinct pairs (0,2) and (1,3) therefore have identical computed quadratic-subfield residue tags in each fiber. These are stronger than a manually assigned fiber label: the tags are calculated from repeated multiplication in the actual finite quadratic quotient. The Lean module prints the transitive axioms of each closed theorem.

## Why these are the correct candidate prime ideals

For E=Q(zeta_20), the cyclotomic integer ring is O_E=Z[zeta_20]. The reduction of Phi_20 modulo 29 splits into the four degree-two irreducible factors above. Each quotient

    O_E / p_j = F_29[X]/(f_j(X))

defines a maximal, hence nonzero prime ideal p_j above 29. Such an ideal determines a HeightOneSpectrum (O E) point. These are established number-field deductions, and their identification with the upstream concrete Lean objects remains to be constructed.

The subfield Q(i) embeds into E via i=zeta_20^5. The images of i under those residue quotient maps are the scalars 17,12,17,12. Hence p_0 and p_2 contract to the same prime of Z[i] while p_1 and p_3 contract to its conjugate. Distinctness of p_0 versus p_2 follows because their f_j are different monic irreducible factors. These furnish explicit finite certificates for the geometric property required by upstream OneK(i) and Apart, subject to construction of the actual prime ideal terms.

## Exact upstream Lean goals still open

The original riemann-hypothesis source uses genuine HeightOneSpectrum (O E), not Fin 4. The next formalization should be performed in a Mathlib-enabled Lean workspace, with the upstream source imported at the pinned commit:

1. Define E=Q(zeta_20) and prove O_E is the cyclotomic integer ring. Construct ring homomorphisms from O_E into the four finite quadratic quotient fields. Identify each kernel as a distinct maximal ideal over 29; convert each to HeightOneSpectrum.
2. Prove the contractions of these ideals to O_{Q(i)} agree precisely for the pairs (p_0,p_2) and (p_1,p_3), using zeta_20^5 and the computed root values. Discharge upstream OneK(i) and Apart with the actual subfield injection and ideal membership equivalence.
3. Prove IsSplitAt p_j at the relevant places and the place-specific local degree. Use the already verified norm and character arithmetic as a target for a local p-adic bridge, retaining the original type of TyEll.
4. Resolve the exceptional-set requirements of SphOffU and GenTy at the original theorem applications; the norm-pullback character ramifies at all four primes over 29, and a single-prime order-29 character is obstructed by the global-unit logarithms of RHD-10C.

**Toolchain boundary:** the pinned upstream riemann-hypothesis repository uses Lean v4.33.1 with Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, while MathCan uses Lean v4.35.0 and imports only Init. Porting the real ideal construction must use a separate upstream-compatible workspace or an explicit Mathlib migration. A MathCan Lean kernel pass alone cannot certify the original source interface.

The project-wide MathCan Lean configuration imports Init without Mathlib. Consequently this PR compiles an actual finite quotient calculation inside the existing kernel rather than disguising the missing number-field and automorphic infrastructure behind arbitrary Prop assumptions.

## Reproduction

Run:

~~~bash
lake env lean MathCan/RHPrimeFibers.lean
~~~

The dedicated CI runs this command with Lean 4.35 and records the axiom output. The build must reject sorryAx and ofReduceBool. It deliberately avoids importing the nonexistent upstream HeightOneSpectrum interface and describes this boundary in the source comments.

There is no proof term for OneK, TyEll, SatU, SphOffU or SeedFinOdd in this module.
