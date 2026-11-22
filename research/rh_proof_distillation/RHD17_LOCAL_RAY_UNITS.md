# RHD-17: exact local ray-unit quotient after dividing global torsion

**Parent:** merged RHD-16 PR #198, with local split-unitary character from RHD-15 PR #195.
**Pinned source:** `leanprover-community/riemann-hypothesis` at `f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`.
**Evidence boundary:** all eight finite quadratic quotient rings are exhaustively enumerated. The real adelic torus, original `UA E 1`, `RU`, `TyEll` and `SatU` are not formalized in MathCan.

## A finite quotient relevant to the global character

For a split place `v` of the maximal real subfield `F=E⁺`, one local component of the norm-one torus satisfies `U(1)(F_v) ≅ E_w^×`. The proposed order-p local character is

```text
chi_w(u) = q_p(N_{E_w/Q_p}(u)) ∈ Z/p,
q_p(x) = -((x^(p-1) mod p²)-1)/p (mod p).
```

To test compatibility with diagonal global integral norm-one units, work in the finite local ring

```text
R_w = (Z/p²)[alpha]/(alpha²+c_w alpha+d_w).
```

For the two unramified degree-two examples, `R_w^×` has `p²(p²-1)` elements. The cyclotomic root `alpha` is a primitive `n`th root (`n=20` or `24`). It generates the diagonal root-of-unity subgroup `μ_n`, which has order coprime to p. The character `q_p∘N` kills `μ_n` and therefore descends to

```text
R_w^× / μ_n.
```

The quotient retains an order-p character with index-p kernel.

## Full enumeration results

The generator `rhd17_local_ray_units.py` visits **every pair of coefficients** in each of eight finite quadratic rings, computes norms and character exponents, and records the full histogram. This covers `4·841² + 4·25² = 2,831,624` ring elements. It explicitly checks that the only nonunits have both coordinates divisible by p, as required by irreducibility of the residual quadratic.

| Field / prime | Units per local factor | μ subgroup | Quotient size | Character kernel in quotient | Image order |
| --- | ---: | ---: | ---: | ---: | ---: |
| Q(ζ20), p=29 | 706,440 | 20 | 35,322 | 1,218 | 29 |
| Q(ζ24), p=5 | 600 | 24 | 25 | 5 | 5 |

At p29 the histogram has exactly **24,360** units at each of the 29 exponents. At p5 every one of the five exponents occurs **120** times.

The generator checks `alpha^20=1` and `alpha^10≠1,alpha^4≠1` for all four p29 factors, and `alpha^24=1`, `alpha^12≠1,alpha^8≠1` for all four p5 factors. These prove that the chosen roots have exact orders 20 and 24 respectively. The code verifies all n powers have character zero and samples independent n-element torsion cosets to confirm root multiplication preserves the norm character.

A deterministic SHA-256 JSON sidecar preserves the histograms and kernel sizes.

## Init-only Lean certificates

`MathCan/RHLocalRayUnits.lean` states the eight factor-specific primitive-root power checks in a common quadratic ring representation, with `#print axioms`. A separate abstract lemma proves that a modular character invariant under right multiplication by a chosen generator stays constant along every finite root orbit. Lean also checks the exact cardinalities and kernel/image ratios above.

The `by decide` power checks are finite kernel computations in explicit quotient-ring arithmetic. The corresponding topological local unit group is not constructed from Mathlib; finite-count lemmas alone do not instantiate `TyEll`.

## The global character extension route

Let `T=Res¹_{E/F}(G_m)` be the norm-one torus and `K=∏_v T(O_{F_v}) × T(F_∞)` its maximal compact product. At the chosen split p-place, `chi_w` is nontrivial; it is trivial on other factors of K. The intersection `T(F) ∩ K` is the global integral norm-one units, a finite group by Kronecker's theorem. For these two CM cyclotomic fields, it is `μ20` or `μ24`.

The exhaustive finite calculation certifies that `chi_w` is trivial on that torsion subgroup, making it a candidate for a continuous character of

```text
K / (K ∩ T(F)) ≅ KT(F) / T(F).
```

Since K is open, this is an open subgroup of the abelian quotient `T(A_F)/T(F)`. The standard divisibility/injectivity theorem for circle-valued characters gives an algebraic extension to the whole quotient; continuity follows from continuity on that open subgroup. RHD-16 explains why the extension's global order may be larger than its prescribed local order.

**To claim this as an actual original Lean theorem**, the following remain: build genuine local completions and their unit characters, construct `T(A_F)/T(F)`, prove the identified K-intersection and openness, instantiate the character-extension lemma with continuity, and realize the resulting function as an original automorphic eigenvector under `RU`.

Then establish `IsAutRepU`, the rank-one local cuspidality clause in `TyEll`, `SatU` at every other split F-place, `SphOffU w0 ∅ U`, and `AutOffT ∅ U`. The merged RHD-12/15 finite `OneK∧Apart` certificates must likewise be lifted to actual `HeightOneSpectrum` points.

These source-level obligations remain open, and there is no RH proof claim.

## Reproduce

```bash
python -m unittest tests.test_rhd17_local_ray_units -v
python -m research.rh_proof_distillation.rhd17_local_ray_units --output rhd17/local_ray_units.json
lake env lean MathCan/RHLocalRayUnits.lean
```
