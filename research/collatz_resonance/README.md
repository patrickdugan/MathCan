# Collatz resonance: exact census and arithmetic prediction

COL-01 through COL-05 study the split map in the supplied manuscript,
*Prescribing cycles in a Collatz-like map by quadratic reciprocity* (25 November
2026). This package incorporates the research note from commit `2e47a562` and
adds executable evidence. [Mathematical proofs](MATHEMATICS.md),
[source provenance](SOURCES.md), [experiment protocol](EXPERIMENTS.md), and
[companion PRs](CROSS_REPO.md) give the full scope.

For positive `d = 1 mod 4`, even integers halve, odd `n = 1 mod 4` go to
`3n+d`, and odd `n = 3 mod 4` go to `n+d`. Removing every power of two after
an odd branch gives a finite absorbing core of `(d+1)/2` odd vertices.

## Replayed reference census

At `d = 160833217 = 29*53*269*389`, a path enumerator and an independent
indegree-peeling enumerator each processed all 80,416,609 odd core vertices.
Both reproduced the recovered CSV byte for byte. The original recovered C++
program returned the same rows, and Python replayed all 137 cycles under the
unaccelerated map.

| Quantity | Replayed value |
| --- | ---: |
| Cycles | 137 |
| Periodic positive integers | 1,869,713 |
| Maximum full-map period | 74,514 |
| Cycles coprime to d | 55 |
| Relative-sign classes | 41 |
| Conserved periodic classes | 95 |

The [full census](data/reference_census.csv) and [receipt](data/verification.json)
include branch statistics. Among unit cycles:

| Triple branches u | Halvings A | Cycles | Full period range |
| ---: | ---: | ---: | ---: |
| 3,546 | 21,230 | 53 | 28,214–28,365 |
| 9,116 | 55,912 | 2 | 74,505–74,514 |

Every unit cycle satisfies `2^A = 3^u mod d`. Its lattice has basis
`(u,A) = (2,885958), (0,2365636)` and index 4,731,272. Nonunit rows pass the
corresponding relation modulo `d/gcd(n,d)`.

## COL-03: a finite prediction pilot

Before enumerating a parameter's cycles, the predictor chooses the lattice
pair with smallest `A+2u` subject to `u>0`, `A>=2u`, `(A-6u)^2<=22u` and
`u` at most the arithmetic count of unit odd core states. It predicts period
`A+2u`. The direction and variance come from a uniform 2-adic input model.

A size-only log-linear baseline was fitted on 171 admissible parameters in
`5<=d<=1025`. Evaluation covers all 1,194 admissible `1029<=d<=8193`. Each target
is the median full-map period of unit cycles at that parameter, weighting
cycles equally. Every evaluation parameter receives a lattice prediction.

| Predictor | Median relative absolute error on larger parameters |
| --- | ---: |
| Slope-six lattice rule | **3.6769891%** |
| Necessary cone only, A >= 2u | 27.5686137% |
| Same lattice, slope-four direction | 39.0259279% |
| Fitted size-only baseline | 49.9032005% |
| Same lattice, slope-eight direction | 60.9779314% |

The primary rule wins against the fitted size baseline at 848 of 1,194
parameters. Its branch pair occurs at 783 parameters and accounts for 3,488
of 5,369 unit cycles. The additional arithmetic controls were specified after
the first result and are labelled exploratory. All retain the same period
conversion. This is a public finite extrapolation study. The rule selecting
a short lattice point remains empirical; realizable branch words require
further dynamical constraints.

The [tail audit](data/pilot_diagnostics.json) records severe failures:

| Evaluation error statistic | Slope-six lattice | Fitted size baseline |
| --- | ---: | ---: |
| Median relative absolute error | 3.677% | 49.903% |
| Mean relative absolute error | 234.603% | 99.825% |
| 90th percentile, nearest rank | 414.932% | 220.780% |
| Largest relative absolute error | 32,250% | 1,805.439% |

At d=4093, the lattice rule predicts 5,176 against a median unit-cycle period
of 16. The exact family d=2^a-3 has an odd fixed point at 1 with
(u,A,r)=(1,a,1). For a>=11, the primary slope band excludes that real cycle.
The [proof](FAILURE_FAMILY.md) establishes an incompleteness of the selection
rule. Typical-period accuracy and severe tail failures are both part of the
result. A robust predictor needs a new design and fresh evaluation.

- [Primary results and fitted coefficients](data/resonance_pilot.json)
- [All 1,365 development/evaluation rows](data/resonance_pilot.csv)
- [Post-result arithmetic controls](data/pilot_controls.json)
- [Independent modular-power and receipt audit](data/independent_pilot_audit.json)

## Formal proofs and the finite memory diagnostic

[`CollatzResonance.lean`](../../MathCan/CollatzResonance.lean) contains 19
declarations checked with Lean 4.35.0. They include positivity and oddness of
the actual accelerated map, finite-core closure, strict descent above the
core, eventual entry, conserved labels along iterates and a decoder
obstruction. The [axiom inventory](data/lean_axioms.txt) uses only `propext`
and `Quot.sound` where axioms occur. Reciprocity and the all-moduli
classification retain written proofs and the scope stated in the note.

A fixed ordered history of branches and exact halving counts determines the
seed modulo `2^(A+1)`. A history of length h is therefore injective on the odd
core whenever `2^(2h+1)>d-1`. Five observations suffice through `d=1025`.
An exhaustive decoder check covers 44,204 odd states. Companion recurrence
experiments include shuffles that preserve observation cell sizes to expose
this finite encoding effect.

The smallest useful alias fixture is `d=13`: seeds 1 and 5 share their
`<2,3>`-orbit and reach distinct odd cycles `[1]` and `[5,7]`. Their first
branch-and-halving observations differ. This connects arithmetic
obstructions to reasoning and value-of-information tasks.

## Reproduce

Run from the repository root with Python 3.10+ and a C++17 compiler:

```sh
python3 -m unittest discover -s tests -p test_collatz_resonance.py -v
c++ -O3 -std=c++17 research/collatz_resonance/census.cpp -o /tmp/collatz-census
/tmp/collatz-census 160833217 path > /tmp/collatz-path.csv
/tmp/collatz-census 160833217 peel > /tmp/collatz-peel.csv
python3 -m research.collatz_resonance.audit_reference \
  --path-csv /tmp/collatz-path.csv --peel-csv /tmp/collatz-peel.csv \
  --output /tmp/collatz-verification.json
cmp /tmp/collatz-verification.json research/collatz_resonance/data/verification.json
python3 -m research.collatz_resonance.resonance_pilot
python3 -m research.collatz_resonance.pilot_controls
python3 -m research.collatz_resonance.pilot_diagnostics --check
lake env lean MathCan/CollatzResonance.lean
```

Path tracing uses about one byte per odd vertex; peeling uses about five.
The default C++ limit is 100 million vertices. All reported runs used local
CPU. Learned recurrent models and paid training runs remain future work.
