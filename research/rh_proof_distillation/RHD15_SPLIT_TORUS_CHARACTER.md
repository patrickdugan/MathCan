# RHD-15: asymmetric split-place U(1) character, finite witness and RLT gym

**Source pin:** [leanprover-community/riemann-hypothesis `f150e026`](https://github.com/leanprover-community/riemann-hypothesis/tree/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src).
**Parents:** merged MathCan RHD-09 through RHD-14; specifically RHD-14 PR #192.
**Evidence boundary:** exact finite local arithmetic and Init-only Lean lemmas. Original `UA`, `RU`, `TyEll`, `IsAutRepU`, `SatU`, `SphOffU`, `OneK` and `SeedFinOdd` are not constructed.

## A positive local rank-one candidate

For a CM extension E/F and a *split* finite place v of F, the local algebra is
```text
E ⊗_F F_v ≅ E_w × E_{bar w},   E_w ≅ F_v,
U(1)(F_v) ≅ { (u,u^(-1)) : u ∈ F_v^× }.
```
The inverse in the second coordinate is transported through the complex conjugation isomorphism. Hence a continuous nontrivial character of `E_w^×` defines a local character of `U(1)(F_v)`, supported at **one F-place** though its two conjugate E-components carry inverse exponents.

In `Q(ζ20)` at `p=29` and `Q(ζ24)` at `p=5`, use the first-layer character
```text
θ_j(1+p(a+bα)) = 2a-c_j b (mod p).
```
Its scalar witness `a=(p+1)/2,b=0` has exponent 1, so the character is surjective onto `Z/p`. The underlying whole-unit character `q_p(N_j(u))` is order p, trivial on the local roots of unity, and can be extended to `E_w^×` by prescribing its value on a uniformizer. These are local observations; the adelic/global extension is the actual next theorem.

The norm-one pair sends `z=(a,b)` at local factor j to `-conj(z)` at factor k. The code checks:
```text
θ_j(z) + θ_k(-conj(z)) = 0 (mod p),
θ_j(z) can be nonzero,
(χ_Q ∘ N_{E/Q}) on the norm-one pair = 1.
```
Thus the local asymmetric character retains a useful eigenvalue even though RHD-14's absolute-norm pullback collapses.

## Key source-level simplification: Apart excludes the conjugate partner

The actual pinned source [ClosedAtLConclusionOfMem.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Development/AbelianVarietyTheory/Statements/EllipticCurveLevels/ClosedAtLConclusionOfMem.lean) defines
```lean
def Apart (w u : HeightOneSpectrum (𝓞 E)) : Prop :=
  w.under (𝓞 (maximalRealSubfield E)) ≠
    u.under (𝓞 (maximalRealSubfield E))
```
so the two conjugate primes above one split F-place have the **same F-contraction**, making `Apart w w0` false for the conjugate partner. In [LatticeDataThicknessBound.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/LatticeDataThicknessBound.lean), `SphOffU w0 S U` demands `SatU` only for split places w satisfying `Apart w w0` and `ApartAll S w`. If the character is ramified only at the selected *F-place*, its conjugate E-prime lies outside the demand and all other split F-places can be unramified.

This suggests using `S=∅` in the `GenTy` and `SphOffU` interfaces. It meets `GenTy`'s requirement that input S avoid p, leaving the hard conditions of actual `SatU`, automorphy and local component existence. The same source's other hypotheses, including `AutOffT` at nonsplit places and universal local cuspidality in `TyEll`, must still be discharged.

The finite factor pairing is:
| Field and p | Conjugate E-prime pairs, each over a single F-prime |
| --- | --- |
| Q(ζ20), 29 | (0,3), (1,2) |
| Q(ζ24), 5 | (0,2), (1,3) |

Each has **two** F-prime orbits, with the partner in the same orbit.

## Global compatibility: a different unit group

At the level of integral norm-one units, `u bar(u)=1` means every complex conjugate of u has complex norm one; Kronecker's theorem implies u is a root of unity. The two fields contain μ20 and μ24 respectively, both of order prime to p=29 or 5. The local p-power characters above vanish on each cyclotomic root; the Python implementation checks all powers directly in the quadratic residue ring modulo p².

This removes the **specific full-rank-unit obstruction** from RHD-13, which concerned single-prime Hecke characters of E required to kill *all* E-units. The norm-one torus's rational points must still satisfy global reciprocity and component/class group conditions. A continuous global torus character with exactly this local type has not been constructed.

## Exact corpus and proof targets

`rhd15_split_torus_character.py` generates `4·29² + 4·5² = 3464` unique root episodes. The 29-adic family is SHA-256 split into train/validation/test, while every p=5 root is held out as `crossfamily_test`. Zero through three independent mutations per episode model five local errors:

- Wrong conjugate factor (different F-place)
- Using the same sign rather than the inverse at the partner
- Replacing the torus character with the trivial absolute-norm pullback
- Incorrect trace coefficient
- Putting another p-adic F-place in the ell-away `GenTy` exception set

The trusted verifier identifies the broken finite gate and an oracle sequence repairs one gate per update. All clean cases end with an explicit `STOP`, allowing a learned stopping policy to be tested. The JSONL contains teacher actions for training; evaluation must hide `oracle_actions`, `oracle_steps`, `oracle_terminal` and expected numeric values, and bill model-visible verifier calls independently. Neither a trained neural RLT score nor an actual automorphic proof is claimed.

`MathCan/RHSplitTorusCharacter.lean` proves eight closed anti-diagonal trace identities over Int, surjectivity of the scalar exponent at 29 and 5, conjugate-prime equalities in a finite F-place labeling, and nontriviality witnesses. This is a genuine Init-only kernel arithmetic module. Its finite labels are **not yet actual HeightOneSpectrum primes**.

## Original-`TyEll` bridge to tackle next

1. Construct the two conjugate `HeightOneSpectrum (𝓞 E)` objects above the chosen F-place and prove their common contraction in the original `Apart` predicate.
2. Identify the actual source `UA E 1`, `RU E 1`, and split-place `cLoc` against an adelic `U(1)` model. Establish the correct inversion convention.
3. Extend `q_p∘N_j` from first principal units to `E_w^×`, then to the adelic norm-one torus subject to global compatibility. Prove the resulting character is admissible and has a nonzero automorphic eigenline.
4. Discharge the compact open torsion-free `J`, surjective `θ`, `χ ≠ 1`, and universal `IsCuspidal` implication in the **original** `TyEll`.
5. Build the local `SatU` objects outside the selected split F-place. Show `SphOffU w0 ∅ U` and `AutOffT ∅ U`, then proceed to the actual `SeedFinOdd` interface.

Reproduce:
```bash
python -m unittest tests.test_rhd15_split_torus_character -v
python -m research.rh_proof_distillation.rhd15_split_torus_character --output rhd15/split_torus.jsonl
lake env lean MathCan/RHSplitTorusCharacter.lean
```
