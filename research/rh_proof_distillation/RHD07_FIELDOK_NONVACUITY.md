# RHD-07: FieldOK nonvacuity at the Galois-row input

Upstream source pin: `leanprover-community/riemann-hypothesis` at `f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`.

## Source-defined gate

`GlobalTheory.CongL.FieldOK E ell d` is defined in `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/LatticeDataThicknessBound.lean` as

```lean
ImQ E d ∧ SqAt d ell ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
  ∀ w, ¬ IsSplitAt w → ((ell : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal
```

`ImQ E d` requires `0 < d` and `∃ x : E, x ^ 2 = -(d : E)`. `SqAt d ell` means `IsSquare (-(d : ℚ_[ell]))`; both are declared in `ApartAllEmpty.lean`. The `OneK x w0 v'` predicate in `GeometricFlagBases/HodgeTrAt.lean` requires prime membership to agree on all integral elements of `ℚ(x)`. `Apart v' w0` requires the two primes to be distinct. The empty set satisfies the separately quantified `NonSplitSet` predicate.

## A cyclotomic instance family

Take `E = ℚ(ζ₁₂) = ℚ(i,√3)`, `F = ℚ(√3)`, and `ell > 3` prime. The integral closure is `O_E=ℤ[ζ₁₂]=O_F[ζ₁₂]`. Over F, ζ has equation `z²-√3 z+1=0`, with derivative `2z-√3=i`, a unit. Thus E/F is unramified at finite primes. Also `[F:ℚ]=2` is even.

Two admissible imaginary quadratic choices are `x=i,d=1` and `x=i√3,d=3`. Hensel's lemma for odd `ell \nmid d` reduces the local `SqAt` check to `-d` being a quadratic residue modulo `ell`.

| ell mod 12 | Factorization of Φ₁₂ mod ell | All primes over ell split in E/F? | SqAt(1,ell) | SqAt(3,ell) | Joint FieldOK + OneK + Apart for x²=-d? |
|---|---|---|---|---|---|
| 1 | 4 linear factors | yes | yes | yes | yes, either d |
| 5 | 2 irreducible quadratics | yes | yes | no | no |
| 7 | 2 irreducible quadratics | yes | no | yes | no |
| 11 | 2 irreducible quadratics | no | no | no | no |

The table concerns the **explicit number-field arithmetic obligations**; it does not supply `TyEll`, `SatU`, `AutOffT`, or a `SeedFinOdd` proof term.

Why the negative cases matter: at `ell ≡ 5 mod 12`, the two primes of E above ell have different contractions to ℚ(i), even though `FieldOK E ell 1` passes. At `ell ≡ 7 mod 12`, the same issue occurs for ℚ(√−3) and d=3. A universal implication can therefore pass `FieldOK` while its intended distinct-prime antecedents lack a witness.

For `ell=13`, the two distinct roots 2 and 6 of `Φ₁₂(x)=x⁴−x²+1` satisfy `2³=6³=8 (mod 13)`. Their √3 residues differ: 9 versus 4. This gives a specific degree-one prime-fiber arithmetic certificate for `OneK(i)` and `Apart`. The Lean goal is to construct these two actual `HeightOneSpectrum (𝓞 E)` objects and discharge the exact predicates.

## New genericity simplification

The upstream `DGen` and `GapJ` definitions occur in `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/LimWPhi.lean`. At rank one:

```
DGen₁(X) = 1
GapJ 1 J = True
```

Here `GapJ` is vacuous because its index premise is `i+1 < 1`. At rank two, exact product expansion yields `DGen₂(X,Y)=XY(X−Y)^8(X+Y)^4`. For nonzero parameters the rank-two genericity test reduces to `X ≠ Y` and `X ≠ −Y`.

The source's `SeedFinOdd` permits any positive odd rank, so `a=1` is a worthwhile first instantiation. The difficult remaining predicate is `TyEll` in `Definitions/Divisors/GenOf.lean`, which includes a compact open torsion-free local subgroup, a surjective homomorphism to `Multiplicative (ZMod (ell^m))` (the additive cyclic group written multiplicatively), a nontrivial character, and an automorphic eigenvector.

## Computational evidence and next kernel gates

An offline deterministic companion corpus has 3,681 supervised finite-ring/integer cases and 906 recurrent verifier-scored corrections, across 237 primes with prime-disjoint train/validation/test splits. All 13 local tests passed, including a SymPy independent factorization sample and full label/trajectory replay. Among 474 pairs `(ell,d)`, 231 pass the arithmetic `FieldOK` shell and 108 also pass the distinct-prime `OneK` shell. There are 123 `FieldOK`-only near misses.

Proposed kernel-checked target sequence:

1. Construct `E=ℚ(ζ₁₂)` and its CM/maximal-real subfield representation in Mathlib, with ring-of-integers and relative different certificates.
2. At `ell=13`, construct the four prime ideals using `Φ₁₂` factors, select the two lying over roots 2 and 6, prove equality of their contractions to ℚ(i) and their inequality.
3. Prove `SqAt 1 13` with a p-adic square root lifting the residue 5, then assemble the actual `FieldOK E 13 1` proof.
4. Construct rank-one automorphic `U` with nontrivial `TyEll` at the chosen place, `SatU`, `SphOffU`, `AutOffT ∅ U`, and the needed weight data. Track these as separate acceptance gates.
5. Instantiate `SeedFinOddOf` with the genuine Lean witnesses. Preserve `proof_term_data=false` until compiled imported proofs are available for this instance.

No statement here asserts a new proof of RH. The source-pinned arithmetic supplies a reproducible nonvacuity test and a search curriculum for actual automorphic witnesses.
