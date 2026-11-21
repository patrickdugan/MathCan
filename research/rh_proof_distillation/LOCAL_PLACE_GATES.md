# RHD-06 | Local place and theta-weight feasibility

Upstream is `leanprover-community/riemann-hypothesis`, pinned at
`f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`. This extends MathCan RHD-04/#151 and RHD-05/#152.

## What the place predicates mean

The published `ClosedAtLConclusionOfMem.lean` definition of `Apart w u`
requires the **restrictions to the maximal real subfield** to be
different:

`w.under (𝓞 (maximalRealSubfield E)) ≠ u.under (𝓞 (maximalRealSubfield E))`.

The published `HodgeTrAt.lean` definition of `OneK x w w'` requires
membership agreement between both prime ideals on integers of E lying
in `ℚ(x)`. `StConj.lean` declares `SameK x w w'` with the identical
normalized proposition body. The RHD-06 source auditor pins both
definitions by exact Git blob and checks source-statement equality.

Thus the geometric premise `OneK x w₀ v' ∧ Apart v' w₀` requires
primes agreeing above the quadratic subfield `ℚ(x)` but lying over
different primes in the real subfield. This is stronger than simply
asking for two distinct primes of E.

For a CM quadratic E whose maximal real subfield is ℚ, the two primes
over a fixed rational prime l cannot satisfy Apart, because ℚ has
only one prime above l. The audit therefore needs a larger CM field.

The `SeedFinOddOf.lean` theorem constructs the geometry input by
moving primes through its `SameOr` lemma, and the audited call to
`GeoOne` explicitly supplies `OneK` from chained `SameK` proofs.

## Concrete finite residue-field compatibility

Choose the biquadratic CM field E = ℚ(i, √5), with maximal real
subfield F = ℚ(√5), and K = ℚ(i). Set x = i, d = 1,
and the rational prime l = 29.

Over the finite field 𝔽₂₉, the two minimal polynomials split:

- `u² + 1 ≡ 0 (mod 29)` has precisely the roots 12 and 17.
- `v² − 5 ≡ 0 (mod 29)` has precisely the roots 11 and 18.

The two reductions `(i, √5) ↦ (12, 11)` and
`(i, √5) ↦ (12, 18)` agree on K and differ on F.
As 29 is unramified in E, these are compatible with the relevant
prime-ideal restrictions. The new Init-only Lean theorem independently
certifies the exact modular roots and distinct/same coordinate pair.

The statement about compatibility of reductions is the scope of this
formal test. The audit has **not** yet constructed the associated
height-one prime objects of `𝓞 E` inside Lean, proved `FieldOK E 29 1`,
or supplied the automorphic antecedents `AutOffT`, `TyEll`,
`SphOffU`, `SatU` and `LacWtAt`. It is consequently a necessary local
witness, rather than a complete nonvacuity certificate for `GeoOne`.

A concrete follow-up in Mathlib is to construct all four primes of E
over 29 and their restrictions to K and F, then verify the exact
`FieldOK` and geometric antecedents used by `seedFinOdd_of`.

## A dimension-sensitive condition in TLiftK

The published `TLift_k` fixes the initial E, B, n and Hermitian X
before selecting an eventual dimension threshold d₀. Its later
quantified data include skew-Hermitian W, Hecke characters, their
exponents, and an input automorphic representation U. Their
antecedents contain the inequality

`(d : ℤ) + mW(w) ≤ 2 * (lam(w)).w(k)`

at each infinite place w and index k. The MathCan Init proof certifies
that when weight is bounded above by L and the twist exponent is
bounded below by M, the admissible target dimensions obey
`d ≤ 2L − M`.

For any **fixed** weight and twist exponent, this condition cannot
hold at every arbitrarily large dimension. The original statement
allows the later data to vary with dimension, so the result is
consistent with the stated eventual lift. It points to a required
nonvacuity test: construct a sequence of later data satisfying the
dominance, Hecke, exponent, automorphy and lift conditions in the
range of d under study.

## Verification boundary

The Python audit pins six original Git blobs, tests the exact source
definitions, and enumerates the polynomial roots modulo 29. The
Init-only Lean file proves the modular and integer-inequality claims,
with an axiom inventory in CI. All claims about geometric packages,
Galois representations, eventual theta lifts and the global RH theorem
remain under their own source and imported-proof validations.

The highest-value next piece is the actual number-field prime
construction, followed by a compatible automorphic U. The source's
full Lean development has independent kernel verification, but our
local tests have a deliberately narrower mathematical contract.
