# RHD-10: rank-one eigenline and finite-character repair gym

**Source pin:** [leanprover-community/riemann-hypothesis at f150e026](https://github.com/leanprover-community/riemann-hypothesis/tree/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src).
**Parent:** MathCan RHD-09, PR #159, merged at 51582b2.
**Proof status:** Init-only integer-scalar eigenfamily theorem, with a separate synthetic finite-ring gate verifier. No complex automorphic representation is imported into MathCan. The original automorphic `TyEll` and `SeedFinOdd` remain unproved.

## Source-accurate original interfaces

[GenOf.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Development/AbelianVarietyTheory/Definitions/Divisors/GenOf.lean)
defines `GlobalTheory.CongW.TyEll` with the following conjuncts, for a selected prime `w₀`:

1. Some `m : ℕ`, compact open subgroup `J ≤ GL(Fin a,E_w₀)`, surjective `θ : J →* Multiplicative(ZMod (l^m))`, and nontrivial `χ : Multiplicative(ZMod (l^m)) →* ℂˣ`.
2. The specified torsion-freeness on `J`; for **every** smooth irreducible local representation `σ`, a nonzero `χ∘θ` eigenvector implies the original `GlobalTheory.SmGL.IsCuspidal σ.ρ`.
3. **An actual** `φ ∈ U`, `φ ≠ 0`, with the source's `RU E a x φ = ((χ (θ ⟨cLoc w₀ x,h⟩):ℂˣ):ℂ) • φ` for every eligible local `x` and `h`.

[LatticeDataThicknessBound.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/LatticeDataThicknessBound.lean)
defines `AutOffT`, `SatU`, and `SphOffU`. The latter requires a genuine `SatU` witness at each split place `w` satisfying `Apart w w₀` and `ApartAll S w`; `SatU` itself existentially quantifies a smooth irreducible local representation with a Satake parameter. `AutOffT ∅ U` includes `IsAutRepU U` and unramifiedness at **every non-split** place.

The source's `GenTy` in [FlagM3PadicGlobal.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Development/AbelianVarietyTheory/Definitions/Divisors/FlagM3PadicGlobal.lean) **additionally requires all places in its input `S` to avoid `l`**. Thus reusing the three ramified primes above 29 as that very `S` does not meet the `GenTy` premise. This is a specific interface conflict to resolve in the eventual global proof, rather than an unnoticed substitution. The distinct `UnitaryWeightCondition` interface has a different quantification over `S`.

## Character and arithmetic model

Take `E=ℚ(ζ₂₀)`, `l=29`, `a=1`. RHD-09 verified four degree-two local factors at 29 and the finite first-layer formula

```text
θ_j(1+29(a+b α_j)) = 2a-c_j b mod 29
q(N(1+29(a+b α_j))) = 2a-c_j b mod 29
q(x) = -((x^28 mod 841)-1)/29 mod 29
```

For each of four places `j`, the scalar `a=15,b=0` supplies `q(N(1+29a))=1`. Consequently the norm-pulled character is ramified at every one of those four places. If `w₀` is one of them, the other three must be omitted from the spherical Satake demand, for instance by the `SphOffU` exception set `S=\{w_j:j≠w₀\}`. These finite indices still need conversion to actual `HeightOneSpectrum (𝓞 E)` places and proofs of their properties.

The candidate global character is a Hecke idele-class character of `ℚ` associated with `q`, composed with the adelic norm `N_{E/ℚ}`. The associated rank-one function is `φ(g)=ω_E(g)`, and algebraically its right translation obeys `R(h)φ=ω_E(h)•φ`. Depending on normalization and the upstream right-action convention, the local character can require an inverse. Fix this against the original `RU` before constructing `J, θ, χ`.

## What the kernel proves in RHD-10

MathCan's Lean 4.35 project imports `Init` and has no Mathlib dependency. `MathCan/RHRankOneEigenline.lean` therefore formalizes the universal algebraic eigenfamily calculation for an abstract type `G`, a supplied multiplication `mulG`, and an integer-valued multiplicative function `χ : G → Int`. The nonzero theorem assumes a unit witness `χ e = 1`.

- `characterFunction χ` belongs to the explicitly defined set `eigenfamily χ` of integer scalar multiples, and is nonzero under the unit witness.
- Every member of the eigenfamily obeys the right-eigenrelation `rightTranslate mulG h f = fun g => χ h * f g`. The family is stable under every such translation.
- Four finite indices are modeled, with a decidable count of precisely three indices other than the selected one.

This is a **kernel-checkable algebraic skeleton**, with integer scalars deliberately used to fit the independent Init-only project. Integers cannot represent the required primitive 29th-root complex character. The `ℂ`-submodule `U`, original `UA E 1 → ℂ` function space, and the adelic bridge remain open proof targets. No field-theoretic claim is inferred from the finite-index count.

## Finite verifier and recurrent correction dataset

`rhd10_rank_one_repair.py` imports the merged RHD-09 exact arithmetic and emits **3,364 input-disjoint root episodes** (four factors times 29² residue-coordinate pairs). The deterministic split is by a SHA-256 hash of `(factor,a,b)`, with one episode per root. Each starts with one, two, or three independent defects selected by committed hashes.

| Fault family | Exact finite witness / gate | Repair action |
| --- | --- | --- |
| Incorrect local coefficient | `θ_j(0,1)=-c_j` | `set_local_coefficient` |
| Wrong global norm sign | `q(N(1+29·15))=1` | `set_global_sign` |
| Lost order-29 conductor | `q(1+29)=1`; conductor 841 | `set_conductor` |
| Failed unit normalization | `q(1)=q(-1)=0` | `set_unit_offset` |
| Missing ramified place | `q(N_j(1+29·15))=1` at every other j | `add_exception` |

The verifier is **complete for this restricted candidate grammar**, since all coefficients, normalization choices, conductor settings and the three exceptional indices have explicitly discriminating probes. It checks mathematical necessities for the proposed globalization, and cannot certify the full existence of a Hecke character, its analytic automorphy, the source `SatU`, or local cuspidality.

Every oracle trajectory repairs one defect per update and ends with the explicit `STOP` action. The manifest records fixed-step teacher success counts at budgets 1, 2 and 3, exact SHA-256, and split counts. These are deterministic synthetic oracle scores; the first trained RLT trial must use unseen root episodes and publish model stop accuracy, verification calls, and zero/one/two/three-step repair rates separately.

## Next Lean interface gates

1. **Real places:** construct degree-two prime ideals of `𝓞 ℚ(ζ₂₀)` from the four Hensel/residue factors and prove `OneK`, `Apart`, and split-place membership on the original `HeightOneSpectrum` interface.
2. **Local group:** construct `J=1+29 𝓞_{E_w}` inside `GL(Fin 1,E_w)`, prove compactness, openness, torsion-freeness, and `θ` surjective onto `Multiplicative (ZMod 29)`; produce the complex character and check the eigenrelation normalization.
3. **Automorphic vector:** realize `ω_E=\widetilde q∘N_{E/ℚ}` as a genuine idele-class character, map the function into `UA E 1 → ℂ`, and assemble the original `U` satisfying `IsAutRepU`.
4. **Representations and Satake:** provide the universal rank-one `IsCuspidal` implication, `IsCompAlong` objects, and `SatU` outside the four ramified primes, including `SphOffU`.
5. **Downstream S reconciliation:** audit where the `GenTy` input set must avoid `l`, and give a different proof route or distinct exceptional sets if necessary before claiming a `SeedFinOdd` instance.

No claim about a Riemann hypothesis proof follows from this work.
