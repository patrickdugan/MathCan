# RHD-09: local norm character and rank-one TyEll route

## Proven finite arithmetic

This follows merged MathCan PR #156 (5a4026ab) and source-pins leanprover-community/riemann-hypothesis at f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3.

For E=Q(zeta_20) and p=29, Phi_20(X)=X^8-X^6+X^4-X^2+1 has four irreducible degree-two factors modulo 29:

| index | coefficient c in X^2+cX-1 (mod 29) | X^5 mod factor |
| --- | --- | --- |
| 0 | 2 | 17 |
| 1 | 14 | 12 |
| 2 | -14 | 17 |
| 3 | -2 | 12 |

Thus the primes from factors 0 and 2 are distinct and contract to the same prime in Z[i], and factors 1 and 3 contract to its conjugate.

The exact simultaneous Hensel lifts modulo 29^2=841 are the monic quadratics X^2+cX-1 with coefficients c=785, 826, 15, 56, respectively. Their product is Phi_20 modulo 841. Reduction gives the four irreducible factors above.

At any degree-two local completion E_w/Q_29, the principal-unit group J=1+29 O_{E_w} has first layer (F_29)^2. For z=a+b alpha, with alpha^2+c alpha-1=0, let u=1+29z. Then

```text
N(u) = 1+29(2a-cb)       modulo 841
theta(u) = Tr(log(u)/29) = 2a-cb modulo 29.
```

The character is surjective: the scalar witness z=15 maps to 2*15=1 modulo 29. The first-layer kernel has size 29, and the full principal-unit subgroup is expected to be compact, open and torsion-free by standard unramified 29-adic theory. Its actual p-adic construction and Lean proof remain open.

## A global character through the norm

For every unit x modulo 841 define

```text
q(x) = -((x^28 mod 841)-1)/29     modulo 29.
```

Fermat makes the integer division exact. The exponent is a homomorphism from (Z/841)^times to the additive Z/29, with q(1+29t)=t, q(30)=1, and q(+/-1)=0. A primitive 29th root of unity converts q into an order-29 Dirichlet character of exact conductor 841. Its local exponent, pulled back along N_{E_w/Q_29}, satisfies q(N(u))=theta(u). The sign of the associated Hecke local component depends on the Dirichlet-Hecke convention; select the upstream nontrivial chi accordingly.

The associated Hecke character of Q, composed with the idele norm N_{E/Q}, gives a concrete global rank-one automorphic character candidate on E. Norms of global algebraic units of E are +/-1, so the character respects the unit compatibility condition.

There are four primes of E above 29, and all four are split in E over the maximal real subfield: the order-2 decomposition subgroup <9 mod 20> excludes complex conjugation 19. The norm-pulled global character is ramified at every one of the four. To meet the source SphOffU w0 S U interface, the finite exceptional set S must contain the **other three** primes above 29. Away from 29 the norm character is unramified, matching the non-split-place unramified condition inside AutOffT empty U.

## Kernel-visible targets and evidence boundary

The original TyEll definition in Development/AbelianVarietyTheory/Definitions/Divisors/GenOf.lean requires:

1. A compact open torsion-free subgroup J of GL(Fin a,E_w), with a surjective group homomorphism to Multiplicative(ZMod(l^m)).
2. A nontrivial complex-valued character and the universal cuspidality implication for local smooth irreducible representations with a J eigenvector.
3. A nonzero actual automorphic eigenfunction phi in the chosen submodule U, with the specified right-action eigenrelation.

For a=1, GL1 has no proper parabolics and hence its local irreducibles are cuspidal in the standard definition. Proving this for the upstream predicate is an explicit remaining Lean task. The submodule U, IsAutRepU, right-action eigenrelation, SatU, and SphOffU all require construction rather than finite arithmetic substitutes. The upstream UnitaryHeckeChar infrastructure in BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean offers candidate building blocks but has not been bridged to TyEll.

Proposed Lean proof slices: identify actual HeightOneSpectrum ideals from the lifted factors and prove OneK/Apart; instantiate m=1 with trace-log and 29th-root chi; globalize through the adelic norm and realize the GL1 automorphic U; construct the three-prime exceptional set and discharge the remaining original interfaces.

The sibling Python generator emits 3,364 exact first-layer finite-ring training examples, with deterministic SHA-256 manifest and input-disjoint train/validation/test splits. Tests cover the full trace/norm identity, Hensel factors, irreducibility, surjectivity, kernel size, character homomorphism and mutation controls. These are **synthetic oracle labels**, not a trained RLT evaluation. Actual Lean proof terms for TyEll, OneK or SeedFinOdd are still missing.
