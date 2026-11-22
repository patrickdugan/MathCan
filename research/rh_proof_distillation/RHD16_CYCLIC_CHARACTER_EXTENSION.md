# RHD-16: finite character-extension order inflation

**Repository:** MathCan, following merged RHD-15 PR #195.
**Source pin:** `leanprover-community/riemann-hypothesis@f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`.
**Evidence scope:** exact cyclic finite group arithmetic, independently checked in Lean Init and Python. The original adelic `UA E 1`, `RU`, `TyEll`, `SphOffU`, `SatU` and `SeedFinOdd` remain unproved.

## Why this gate matters

RHD-15 identified a nontrivial order-`p` character at a selected split place on the first principal-unit layer of `U(1)`. Extending a continuous character from an open subgroup of an abelian adelic quotient is a standard divisible-target argument, but its extension can have **higher global order**.

The simplest exact example is

```text
G = Z/(p²),   H = pG ≅ Z/p.
lambda(p) = zeta_p,  where zeta_p is a primitive pth root.
```

Every homomorphism `G → μ_p` sends the element `p` to `ψ(1)^p = 1`, preventing it from restricting to `lambda`. In contrast, the homomorphism `ψ : G → μ_(p²)` with `ψ(1)=ζ_(p²)` sends `p` to `ζ_p` and supplies an extension.

Writing a character of `G` as the exponent `e` of the primitive `p²`-th root and allowing any local target exponent `t∈Z/p`, the extension condition is precisely

```text
(p*e) mod p² = p*t
       iff
e mod p = t.
```

For every `t`, there are exactly `p` global exponent choices `e=t+p k` for `k∈[0,p)`. When `t≠0`, all those exponents are coprime to `p` and have exact order `p²` as characters of `G`. An order-`p`-only global search would miss every one of them.

This **does not require the local `TyEll` character `χ` to have order `p²`**. The pinned `TyEll` explicitly allows local characters through `Multiplicative (ZMod(l^m))`, and the global automorphic character providing its eigenvector can have larger order.

## Exact Lean kernel targets

`MathCan/RHCyclicExtension.lean` imports only `Init` and the merged RHD-14 finite torsion compatibility lemma. Its theorems establish, for `p=5` and `p=29`:

- `Extends p e t ↔ e mod p=t` for finite exponent choices;
- existence of `p²`-root extensions for *every* local exponent;
- impossibility of a `μ_p`-valued global extension of a nontrivial character on `H=pG`;
- primitive residue constraints for a local target of exponent one;
- p-primary root-of-unity compatibility for `μ24` and `μ20`.

The theorems concern the explicitly defined cyclic groups. The relevant topological extension lemma for `T(A_F)/T(F)`, the cyclotomic norm-one unit intersection, and the original automorphic realization still need imported Lean proofs.

## Exact verifier and 866 synthetic repair episodes

`rhd16_cyclic_extension.py` enumerates all possible ambient exponents for the two primes, checking the number and primitive order of valid extensions for every local character. Three independent mutation types define the repair curriculum: an insufficient root-of-unity codomain order, an incorrect ambient generator exponent, and a nonzero p-primary twist on the global cyclotomic roots of unity.

The emitted JSONL contains one episode per candidate root `e∈Z/p²`: **841** at `p=29`, and **25** at `p=5`. The larger family has SHA-256-disjoint train, validation, and test splits; all 25 cases at `p=5` are held out as `cross_prime_test`. Each episode has zero to three injected faults, a verifier-scored oracle correction trajectory, and an explicit terminal `STOP`.

The repair traces constitute synthetic arithmetic supervision. They contain the gold actions and expected terminal states for offline training; a model evaluation must redact those fields and count only model-visible verifier calls. **No neural or recurrent model scores have been produced.**

## Remaining original proof construction

RHD-15's next global step uses `G=T(A_F)/T(F)` for the norm-one torus `T=Res^1_{E/F} G_m`. Choose a compact open finite-adelic subgroup `K` supporting the local character at the chosen split `F`-place and trivial components elsewhere. Check `K∩T(F)`, consisting of norm-one global integral units under the stated maximal-compact conditions, and show the local character kills it. The root-unit checks in RHD-15 address the finite torsion part of that compatibility.

To obtain an actual global automorphic eigenline, construct the open subgroup `K T(F)/T(F)` of the adelic quotient and extend its circle-valued character to the entire abelian quotient. Its possible increase in character order is permitted by the abstract extension theorem. Then transport that character to the original `UA E 1` function space, identify the `RU` convention, and prove the original `IsAutRepU`, `TyEll`, `SatU`, `SphOffU w0 ∅ U` and `AutOffT ∅ U` requirements.

The existing RHD-12/15 transverse `OneK ∧ Apart` **finite arithmetic** is the geometric companion, with actual `HeightOneSpectrum` witnesses still open.

Reproduce:

```bash
python -m unittest tests.test_rhd16_cyclic_extension -v
python -m research.rh_proof_distillation.rhd16_cyclic_extension --output rhd16/cyclic_extension.jsonl
lake env lean MathCan/RHCyclicExtension.lean
```
