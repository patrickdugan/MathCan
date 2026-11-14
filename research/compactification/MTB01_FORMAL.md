# MTB-01: finite Markov/Brenier kernel bridge

Date: November 14, 2026. Companion to Compactification Theory's
Markov transport monitoring campaign, pairing:

- OpenAI Math #327, Markov type characterizes superreflexivity
- OpenAI Math #374, sharp one-third Brenier map stability

## Kernel-checked finite results

MathCan/MarkovTransport.lean uses only the pinned Lean 4 Init
library and ordinary kernel-checked proofs. The four-dimensional
hypercube is enumerated using an integer recursion for the number
of coordinate-flip paths with each Hamming weight.

At time four, the exact count vector for Hamming weights 0..4
is (40,0,192,0,24) out of 4^4=256 equiprobable paths.
It follows that E H_4=15/8 and E H_4²=9/2.
For an l1 distance, E H_1²=1, so the four-step
Markov-type-2 squared-constant lower bound is 9/8>1.
In the Euclidean embedding, squared distance is Hamming,
so E H_4=15/8 satisfies the type-2 constant-one estimate.

The arithmetic proof also certifies denominator-cleared exact
two-step affine rectangle transport:
retention q=(3/4)^2=9/16, target W2²=1/3, cross
drift²=53/96, same-map drift²=7/48, and one-step
same-map energy 1/12. It checks the corresponding
threshold-decision flip probability 23/64.

The independently added MTB-01B control gives a sixteen-state
directed square-perimeter walk, stationary under the uniform
law but nonreversible. One-step squared Euclidean
displacement is 1; four-step displacement is 11,
violating the reversible type-2 bound of four.
Lean checks the exact integer squared-distance
sums over all sixteen lattice states.

## Separate proof scopes

The general combined temporal/target-shift theorem in the
Compactification Theory THEORY.md follows from the source
#374 L2 transport stability inequality, Minkowski, and
the Markov-type-p inequality, assuming the latter applies
to the stationary reversible source process.

The general Banach-space superreflexivity criterion from
#327, the optimal 1/3 exponent construction from #374,
the arbitrary-parameter rectangle integration formula,
the all-n hypercube Markov-type lower bounds, and
the all-m directed-square drift identity are **not**
formalized in this small Lean module. They have
separate analytic proofs and executable exact
rational finite checks in the companion branch.

The finite source example uses uniform target rectangles
with affine Brenier maps. That restricted family enjoys
linear transport stability and is not a sharpness witness
for the general source one-third exponent.

The original Q5 LoopedTransformers weights, SAEs,
neural model activations, and production control
systems are not used by this synthetic experiment.

## Reproduction and trust

MathCan.lean imports MarkovTransport.lean. The original
mathcan-proof-audit workflow checks the new module's
transitive axioms alongside existing proofs, and the
dedicated mtb01-markov-transport.yml job compiles
the finite certificate directly. No admitted sorries
or native reduction shortcuts are permitted in
these workflows.

A prior first-pass Rat-proposition elaboration
issue and a duplicate doc comment were corrected
before the final green kernel workflow. Those
changes leave the established four-bit hypercube
and directed-square numerical claims unchanged.

Both new research branches remain draft and unmerged
pending review.
