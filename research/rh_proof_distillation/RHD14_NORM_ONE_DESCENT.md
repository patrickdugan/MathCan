# RHD-14: the absolute-norm character collapses on a norm-one torus

**Source baseline:** `leanprover-community/riemann-hypothesis` at `f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`.
**Parent:** merged MathCan RHD-09 through RHD-13.
**Proof status:** exact finite Hensel-factor conjugation, all first-layer norm-character comparisons, and Init-only modular trace identities. The original upstream `UA`, `RU` and `TyEll` are not imported.

## Mathematical correction to the RHD-09 candidate

RHD-09 proposed `omega_E = chi_Q ∘ N_{E/Q}`, obtained by pulling a Dirichlet/Hecke character on Q through the absolute idele norm of E. This gives a perfectly legitimate rank-one character on E ideles when the Hecke globalization is supplied, but its restriction to the *norm-one torus*

    U(1) = ker(N_{E/F}: Res_{E/F} G_m → G_m),     F=E^+,

is trivial:

    N_{E/Q}(x) = N_{F/Q}(N_{E/F}(x)) = 1  for x∈U(1).
    omega_E(x) = chi_Q(1) = 1.

If the source's `UA E 1` is realized through this norm-one unitary torus, then the proposed character `omega_E` supplies only a **trivial** `U(1)` eigencharacter. The local `TyEll` requirement explicitly has `chi ≠ 1`. This calculation therefore rules out the original norm-pullback **as a direct rank-one unitary character witness**, under the stated identification. An exact source-type bridge is needed before asserting the mismatch as a compiled Lean contradiction.

The distinction matters: a character of `GL_1(A_E)` and an automorphic character of `U(1)(A_F)` are different objects. The target Lean `TyEll` is stated over `U : Submodule ℂ (UA E a → ℂ)`, with local `GL(Fin a,E_w)` right actions at split places. The upstream [GenOf.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Development/AbelianVarietyTheory/Definitions/Divisors/GenOf.lean) and [MatchOffTEmpty.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/MatchOfMatchOffTEmpty.lean) are pinned dependency interfaces for verifying that correspondence.

## Exact local conjugation and finite-norm calculation

For E=Q(zeta_20), p=29, the four degree-two Hensel factors `X²+c_j X-1` have coefficients

    (c0,c1,c2,c3) = (785,826,15,56) (mod 841).

For E=Q(zeta_24), p=5, the corresponding factors have coefficients

    (11,2,23,14) (mod 25).

In both families `c_j + c_{j'} = 0` modulo `p²` precisely for the involution `j↔j' = (0 3)(1 2)`. Since `alpha_j^(-1) = alpha_j + c_j` in the local quadratic quotient, the conjugation map can be expressed on coefficient pairs as

    a+b alpha_j ↦ (a-c_j b)+b alpha_{j'}.

It preserves the quadratic norm, hence the rational base-field character exponent. On the first principal-unit layer, for all `a,b in F_p`,

    theta_j(a,b) = 2a-c_j b (mod p)
                  = theta_{j'}(a-c_j b,b).

The difference of the norm-pullback character and its conjugate has exponent **zero**. This is the local version of the global norm-one cancellation.

The Python generator `rhd14_norm_one_collapse.py` checks all `4·29² + 4·5² = 3464` first-layer cases. It independently samples full quadratic quotient norms modulo p², and verifies every conjugate pairing and nontrivial individual local character witness. Deterministic JSONL and SHA-256 receipts are produced.

The Init-only Lean module `RHNormOneCollapse.lean` proves eight coefficient-level congruences and a conditional norm-kernel lemma. This does not build the original local topology or automorphic eigenfunction.

## A route that remains mathematically open

A character directly on the **norm-one unitary torus**, locally nontrivial at one chosen split place, need not be the restriction of `chi_Q ∘ N_{E/Q}`. It should be constructed from genuinely asymmetric local data compatible with the unitary torus's global rational points.

For a CM field E with maximal real F, the group of integral norm-one units is finite: `u\bar u=1` forces every complex conjugate of u to have absolute value one, so Kronecker's theorem makes u a root of unity. For these two cyclotomic fields, the obvious root-of-unity groups have orders dividing 20 and 24 respectively, coprime to the selected p. A p-primary local character is automatically trivial on this finite subgroup.

This changes the relevance of RHD-13's full-rank global-unit obstruction. RHD-13 constrains **Hecke characters of E supported at one prime with trivial infinity type** because they must annihilate all global units of E. The norm-one torus has a smaller arithmetic unit group. The same two global units used by RHD-13 generally have `u\bar u ≠ 1`; they do not supply the same obstruction to a U(1) automorphic character.

The next bridge should therefore construct characters of the adelic norm-one torus, settle the finite class-group / component compatibility and the source automorphic conditions, then supply the original `J,theta,chi` and local `RU` eigenvector. It must continue to check the `SphOffU` and `GenTy` exceptional-set contracts.

## Evidence limits

- **Lean:** concrete first-layer congruences and the conditional trivial-on-norm-kernel statement.
- **Finite arithmetic:** all 3464 comparisons in two separate cyclotomic fields, with local norms and nontriviality controls.
- **Mathematical deductions:** absolute norm is trivial on U(1), and norm-one global units are torsion in CM fields.
- **Unproved in the original kernel:** type equivalence between `UA E 1` and this U(1) model, the local right action `RU`, any actual automorphic representation `U`, `TyEll`, `SatU`, `OneK`, and `SeedFinOdd`.

Reproduce:

~~~bash
python -m unittest tests.test_rhd14_norm_one_collapse -v
python -m research.rh_proof_distillation.rhd14_norm_one_collapse --output rhd14/norm_collapse.json
lake env lean MathCan/RHNormOneCollapse.lean
~~~
