# RHD-13: finite global-unit saturation and formal annihilator certificates

**Repositories / predecessors:** MathCan RHD-09 (#159), RHD-10 (#169), RHD-11 cross-family transfer (#172), RHD-12 finite prime fibers (#174).
**Pinned upstream interface:** `leanprover-community/riemann-hypothesis` at `f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3`.

## New proof artifact

`MathCan/RHFiniteUnitObstructions.lean` imports only Lean `Init`. For each of eight explicit pairs of first-layer global-unit logarithm vectors, it kernel-checks that the **only** coefficient pair `(a,b)∈F_p²` annihilating both vectors is `(0,0)`. Four instances lie over `p=29` in `Q(ζ20)`, and four over `p=5` in `Q(ζ24)`. The argument is closed finite arithmetic, with `#print axioms` for all eight theorems.

The original vectors are computed independently by the already-merged RHD-10C and RHD-11 Python generators. `rhd13_unit_bridge.py` cross-checks all eight vectors and their determinants against the source receipts, then **enumerates every nonzero F_p-linear functional** to make sure it detects at least one of the two units. The resulting JSON and SHA-256 receipt are independently tested.

| Family | Local factor determinant values | All units in F_p? |
| --- | --- | --- |
| Q(ζ20), p=29 | 16, 26, 26, 16 | yes |
| Q(ζ24), p=5 | 2, 4, 1, 3 | yes |

Every determinant is invertible modulo p. In particular, the two unit-log vectors form a basis of each local first principal-unit layer.

### Why this constrains the globalization strategy

Suppose a finite-order p-power Hecke character of the CM field E is unramified at every finite prime except one chosen w above p, and has trivial infinite component. Its restriction to local units at w must annihilate the diagonally embedded global algebraic units. The residue-field unit group has prime-to-p order, and its pro-p principal-unit quotient is a free Z_p-module of rank 2 for these unramified quadratic local extensions. The two concrete global units have logarithm vectors with unit determinant modulo p; by the standard p-adic logarithm and Nakayama argument, their projections topologically generate that pro-p quotient. A continuous p-primary character trivial on those two units is then unramified at w.

This is a mathematical obstruction to the proposed **single-ramified-prime finite-order p-power character** in these two examples, given the stated infinity and support assumptions. The p-adic logarithm, density statement, Hecke character and place restrictions remain **unformalized** in this repo.

It leaves the possibility of more complicated automorphic types, characters with nontrivial infinite type or alternative fields. The original `TyEll` local χ is p-power torsion, but its required U need not arise from the particular finite-order norm-pullback candidate.

## Immediate consequences for source interface research

The explicit RHD-09 norm-pullback of a conductor 841 Dirichlet character ramifies at all four primes above 29. RHD-11 independently demonstrates the analogous four places at conductor 25. The pinned RH source has a `SphOffU w₀ S U` exceptional set, while its `GenTy` interface separately requires every member of the input S to lie away from p. Using the three other ramified primes in the same S meets one requirement but violates the other.

A next construction should track whether **the identical S** is passed through the decisive theorem application, then search for a legitimate automorphic U satisfying both predicates. The finite unit obstruction gives a reason to avoid the easy single-place finite-order character replacement for these cases.

## Formal/evidence boundary

- **Kernel checked:** eight finite `Fin p` annihilator implications, assuming the explicitly given vectors.
- **Executable evidence:** RHD-10C and RHD-11 exact local unit calculations, checked again by RHD-13, including all 8 determinants and brute-force functional enumeration.
- **Outstanding mathematics:** actual cyclotomic number field and integer-ring objects, genuine local completions, global units and p-adic logarithms as Lean structures, continuous characters and local-to-global class field theory, `HeightOneSpectrum`, `OneK`, `TyEll`, `IsAutRepU`, `SatU`, `SphOffU`, and `SeedFinOdd`.

Reproduce in MathCan:

~~~bash
python -m unittest tests.test_rhd10_unit_obstruction tests.test_rhd11_crossfamily tests.test_rhd13_unit_bridge -v
python -m research.rh_proof_distillation.rhd13_unit_bridge --output rhd13/unit_bridge.json
lake env lean MathCan/RHFiniteUnitObstructions.lean
~~~

Use the ordinary MathCan CI to audit the finite proofs and the source data separately. Neither the finite tables nor the Init theorem establishes the original RH argument.
