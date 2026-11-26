# E6: the next geometric lemma

Use the actual point and function-field definitions in Mathlib v4.35.0,
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The project is in
`experiments/trr08_geometry`. Lean 4.35.0 already checks
`TRR08Geometry.tame_coefficient_exclusion`; its remaining inputs are
`hconstant` and `hcocycle`.

## Exact target

Let `K` be a field of characteristic zero or greater than three, let

\[
E:y^2=x^3+Ax+B
\]

be smooth, and let `T` have odd prime order `N ≥ 19`. Assume
`n = (N : K) ≠ 0`. Set `G = ⟨T⟩` and `S = G \ {O}`. Choose one point
from each pair `{P,-P}` in `S`, and let `X` be the set of their distinct
x-coordinates. Define

\[
\Phi(U)=\prod_{v\in X}(U-v),\qquad
\lambda_P=\frac{1}{2y(P)\Phi'(x(P))},
\]

and define the coefficient directly by the finite expression

\[
a_P=-\frac{3x(P)^2+A}{2y(P)}
     -2y(P)\sum_{v\in X\setminus\{x(P)\}}
                      \frac{1}{x(P)-v}.
\]

The order hypothesis makes every denominator nonzero. Extend to a function
`a : ℕ → K` by evaluating at `kT` when it is nonidentity and assigning zero
at identity multiples.

Prove the following statement in Lean using that explicit coefficient:

\[
\forall k,\quad kT\ne O\ \land\ 2kT\ne O
\Longrightarrow
a(2k)=2a(k)+n\frac{3x(kT)^2+A}{2y(kT)}.
\]

This discharges `hcocycle` in the existing compiled curve theorem.
The marked-point order, group law and coordinates must refer to the actual
Mathlib curve throughout the proof.

## Written derivation available for formalization

Let `w = 1/Φ(x)`, use the invariant derivation `∂` with
`∂x = 2y`, `∂y = 3x²+A`, and put `L = ∂w/w`. For a nonidentity subgroup
point `P`, the written proof establishes the rational-function identity

\[
L(Z+P)-L(Z)
 =a_P+n\frac{y(Z)-y(P)}{x(Z)-x(P)}.
\]

It uses `div(w) = N[O] - ∑_{R∈G}[R]`, cancels the principal parts at
`O` and `-P`, and identifies the remaining constant at `O`. Comparing
constant terms at `Z=P` gives the target. The displayed quotient has a
removable value at `P`, equal to the tangent slope.

The full derivation and the local expansion identifying the finite formula
for `a_P` are in [`../trr07/uniform_probe.md`](../trr07/uniform_probe.md).
An algebraic proof directly from finite rational identities would also
discharge the target.

## Following bridge

Once the coefficient construction and cocycle are checked, assume

\[
\sum_{Q\in S} f_0(P+Q)\lambda_Q=u\lambda_P
\qquad(P\in S),
\]

where `f₀(O)=0` and `f₀(P)=x(P)` elsewhere. Derive the existence of
`c : K` such that

\[
a_P^2=n(x(P)+c)\qquad(P\in S).
\]

That is `hconstant`. Applying the existing
`tame_coefficient_exclusion` then proves the tame eigenvector exclusion
on actual smooth curves.

## Required output

Commit Lean source with an explicit theorem type and a build command for
the pinned project. Print its transitive axiom dependencies and retain the
current allowed set: `propext`, `Classical.choice`, `Quot.sound`.
If a library construction is still missing, state its exact type and
which part of the derivation requires it. Record such an item as an open
proof obligation. The current verifier and review distinguish these
premises from the proved curve and polynomial steps.
