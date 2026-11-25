# Exact symbolic experiments at the next marked orders

`symbolic_generic.py` derives the Tate recurrence in the rational function
field using FLINT. Its exact factorization of the numerator of
`x((N-1)/2)-x((N+1)/2)` leaves one monic factor after removing the recorded
powers of `r`, `r-1`, `t`, and `t-1`. On a smooth curve with a point of exact
prime order at least seven, these removed factors are units, as in the
TRR-05 chart argument. All recurrence denominators are saved.

The independently computed new ranks of the finite algebra over `Z[t]` are
6, 9, 14, and 16 at orders 19, 23, 29, and 31. Their defining polynomials have
`t` degrees 9, 13, 21, and 24. Derivation of these equations is a chart
checkpoint; exclusion requires the later elimination and fibre checks.

## Search and replay

The search requires PARI/cypari2 and `python-flint==0.9.0`. Replay requires
Python with that FLINT version and Node 22. For example:

```sh
python symbolic_search.py --order 19 --seconds 900 --memory-mb 768 --output results
python symbolic_replay.py results/certificate19.json
```

The search writes a receipt after each completed stage and retains a partial
certificate. The parent process kills the worker at the specified budget.
`timeout` and `error` receipts leave the mathematical case unresolved.
A successful search status is `exclusion_candidate` until replay succeeds.

The search uses the written residue identity to compress the equations,
computes norms to `Z[t]`, and obtains an integral Bezout identity with a
bounded-degree Hermite normal form calculation. The certificate integer is
sufficient; its minimality is unclaimed. Every denominator of a compressed
ratio must be a recorded power of `t` and `t-1`.

For each prime dividing the integer, the search factors the common norm gcd
over the prime field. In each resulting residue field it computes
`Gamma = gcd_r(f, g_2, ..., g_n)` and tests divisibility of
`Delta^max(1,deg(Gamma))` by `Gamma`. The power accounts for nonreduced
fibre multiplicities. This proves that every geometric fibre root is singular, including
roots requiring further extension fields. An empty gcd fibre is permitted.

`symbolic_replay.py` independently reconstructs the generic chart with FLINT.
The adapted `symbolic_verify.mjs` then uses the original TRR-05 BigInt
arithmetic to rebuild `H`, the residues, compressed equations, and norms. It
checks the integer Bezout identity and matrix identity, verifies irreducibility
and completeness of the finite-field norm factors, recomputes each fibre gcd,
and checks the discriminant remainder. Generic chart coverage still uses the
written Tate-normalization argument. The geometric translation from the
eigenvector obstruction to the interpolation degree remains the TRR-03
premise. A successful run establishes the exclusion within this model.

The original supplied TRR-05 files are unchanged. The adapted replay has
passed against the original certificates at orders 7, 11, 13, and 17.

## Interpretation of the stored data

All polynomial coefficient arrays use increasing powers. Bivariate elements
have an outer `r` array and inner `t` arrays. Finite residue-field coefficient
arrays use increasing powers of the root of the stored irreducible `phi`.
`genericN.json` records multivariate terms as exponent pairs and exact
coefficients. `receiptN.json` records stage timing, norm degrees and coefficient
heights, and the integer and all candidate characteristics if reached.

Tests over small prime fields at the end of Node replay are calibration
checks. The polynomial identities and complete fibre analysis provide the
algebraic-closure exclusion.
