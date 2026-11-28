# DEL-05: variable-extension tensor-power limit in Lemma 2

**Source:** [Hexagon 2611.00789v1](https://hexagonmath.org/2611.00789v1), page 4, Lemma 2.
**Date:** 2026-11-22.
**Repository:** patrickdugan/MathCan, Mathlib 4.35 isolated project.
**Relation:** DEL-04 established finite complex spectral growth using Vandermonde isolation.

## Exact quantifiers in the paper

Let V be a finite-dimensional Q_l vector space with automorphism F and let
a be real. For infinitely many integers k >= 1 assume a positive integer
e_k, a finite-dimensional auxiliary module K_k with automorphism Phi_k,
a sign epsilon_k in {+1,-1}, real C_k > 0, real c_k >= 0, and complex R_{k,n},
such that for every integer n >= 1,

\[
\varepsilon_k R_{k,n} =
  \iota\operatorname{Tr}(F^{e_k n}|V^{\otimes k})+
  \iota\operatorname{Tr}(\Phi_k^{n}|K_k),
\]

\[
|R_{k,n}|\leq C_k q^{e_k n(ka+c_k)}.
\]

The required sublinear loss is \(c_k/k\to0\) **along those admissible k**.
The conclusion is \(|\iota\alpha|\leq q^a\) for every eigenvalue alpha of F.

## Formalized analytic/spectral interface

The Lean 4.35 files add:

- Deligne04/PowerLimit.lean: cancel_extension_degree,
  relative_error_limit, exponent_budget_limit, and
  paper_exponent_normalization.
- Deligne04/TensorLimit.lean: indexed_spectral_bound,
  indexed_spectral_bound_integer_multiplicity, and
  indexed_spectral_bound_paper_formula.
- Deligne04/AllPowers.lean (DEL-04): fixed-spectrum positive-power bound.

An admissible infinite subset of natural-number tensor powers is represented
by a **strictly increasing enumeration** k : Nat -> Nat. For each enumeration
index j, the formal assumptions include a separately chosen e_j > 0, c_j >= 0,
C_j > 0 and eps_j in {1,-1}, a finite spectrum indexed by Fin (s j),
pairwise-distinct complex eigenvalues lam_j, and positive natural
multiplicities m_j. The target eigenvalue alpha^(k_j e_j) must occur in
that spectrum. For all n > 0, the signed trace sum and the remainder
bound must hold.

The paper's automorphisms, tensor products, auxiliary module
and extension of scalars are abstracted **only into those explicit
spectral occurrence and trace-identity assumptions**. The formalized
theorem is therefore an abstract *spectral implication*,
not a construction of the actual geometric modules.

## Proof route

For fixed j, apply DEL-04 to the finite spectrum with positive weights.
Its all-powers hypothesis follows from the signed trace identity
because \(|\varepsilon_j|=1\) and the remainder bound holds for every n.

The resulting spectral estimate is

\[
|\alpha|^{k_j e_j}\leq
q^{e_j(k_j a+c_j)}.
\]

The exponent is equivalently expressed in Lean as
\((q^{e_j(k_j a+c_j)})^n=q^{e_j n(k_j a+c_j)}\).
For q > 0 and k_j,e_j >= 1, monotonicity of positive powers gives

\[
|\alpha|\leq q^{a+c_j/k_j}.
\]

If alpha is zero, the conclusion follows from positivity of q^a.
Otherwise take logarithms and let j tend to infinity. The sequence
c_j / k_j tends to zero by hypothesis, giving

\[
|\alpha|\leq q^a.
\]

The constants e_j, the dimensions of K_j and C_j may vary with j.
This preserves the paper's actual quantifier order.
Strict monotonicity certifies that the enumerated values of k are
distinct and unbounded.

## Formal boundary

The Lean result proves the displayed abstract implication **conditional
on its explicit spectral premises**. These remain separate obligations:

- Construct the genuine l-adic cohomology and auxiliary vector
  spaces K_k, and identify their traces by Gysin exactness.
- Derive from the original Q_l-linear automorphism and its tensor
  powers that alpha^(k e_k) occurs in the combined spectrum.
- Formalize the bridge from the paper's infinite admissible set of k
  to the particular increasing enumeration used here.
- Formalize the weak Lefschetz and geometric hypotheses.

The underlying geometric argument in Hexagon is AI-generated and was
reported as awaiting human verification at publication. The Lean
kernel certifies its *translated abstract spectral implication*,
with the listed geometric premises left explicit.

## Independent exact-rational mutation corpus

The file del05_tasks.jsonl contains 62 deterministic finite examples.
The standard-library checker verify_del05_tasks.py and
tests/test_deligne05_extension_limit.py validate them exactly.

- 30 valid finite shadows with varying positive e, bounded by real
  q-powers, and a symbolic family property c^2 <= k that implies
  c/k -> 0 as k -> infinity for the explicit family.
- 8 linear-loss mutants with c_k=k.
- 6 zero-extension mutants where e_k=0.
- 6 first-power-only mutants passing at n=1 and failing at n=2.
- 6 virtual-trace cancellation mutants with negative multiplicity.
- 6 missing-target-eigenvalue mutants.

These are exact finite witnesses and adversarial cases for DataGoblin.
They are independent of the Lean proof.

## Acceptance gate

Run the dedicated DEL-05 GitHub workflow with Lean/Mathlib 4.35,
inspect the printed axioms and require absence of sorryAx and
ofReduceBool. Independently require the repository-wide MathCan
tests and exact-corpus check.

The next mathematically substantive work belongs to the
geometry-to-spectrum interface, especially the Gysin trace identity
and the tensor eigenvalue occurrence, with hypotheses pinned
to Proposition 4 and Lemma 8.
