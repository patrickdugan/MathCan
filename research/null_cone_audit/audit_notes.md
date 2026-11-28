# NCG audit: the dimension inference

## Source map

Source: [Chandrasekaran, arXiv:2611.34924v1](https://arxiv.org/html/2611.34924v1), accessed 2026-11-26.

The paper constructs a pure GNS extension in Section 4.2; footnote 20 leaves equivalence among choices open. Equation 4.30 bounds a matrix element after one identity insertion. Section 5.2 bounds area by a clock restriction, obtains a positive lower bound on the reflected operator in 5.30, and derives finite dimension through a signed gluing argument in 5.38. Appendix D.3 counts radiative excitations around a spherical background at one loop. Appendix E.1 includes finite closed amplitudes among its axioms; E.3 invokes Section 5.2 when verifying this condition for causal diamonds.

## An exact lemma suitable for formalization

Let H be a Hilbert space and W a bounded positive operator. Assume the ordinary Hilbert-space trace satisfies Tr(W) = Z < infinity, and W >= m I for a real m > 0. Then dim(H) <= floor(Z/m).

Proof: For any orthonormal list e_1,...,e_N,

    m N <= sum_i <e_i, W e_i> <= Tr(W) = Z.

An infinite-dimensional Hilbert space admits finite orthonormal lists of arbitrarily large length. Choosing N > Z/m yields a contradiction. This argument also establishes the stated quantitative bound in finite dimension.

For a bounded self-adjoint A with 0 <= A <= A_max I, functional calculus gives exp(-beta A) >= exp(-beta A_max) I for beta > 0. A trace bound Z then gives dim(H) <= exp(beta A_max) Z. A positive continuous multiplier f on [0,A_max] replaces the lower bound with exp(-beta A_max) min(f).

The ordinary trace matters. A normalized trace on a type II algebra can satisfy tau(I)=1 on an infinite-dimensional Hilbert space. Each theorem and certificate must record the trace convention.

## Countermodel: finite entropy and effective dimension

On ell^2(N_0), set rho e_n = 2^(-(n+1)) e_n. The geometric series gives Tr(rho)=1. Differentiating that series gives

    S(rho) = log(2) sum_(n>=0) (n+1) 2^(-(n+1)) = 2 log(2).

Every eigenvalue is positive, so the rank is countably infinite. Purity is sum_(n>=0) 4^(-(n+1)) = 1/3, and its inverse is 3. Thus a bounded effective dimension can coexist with an infinite support. The eigenvalue infimum equals zero; this is the hypothesis the exact lemma above excludes.

The accompanying script evaluates finite slices using rational arithmetic. Their ranks increase while entropy tends to 2 log(2) and inverse purity tends to 3. Any learned compression task should report exact rank, truncation error, and effective dimension separately.

Generate a receipt with `python operator_countermodels.py --output operator_countermodels.json`, then replay it with `python operator_countermodels.py --check operator_countermodels.json`. The replay gate checks exact fractions, symbolic entropy formulas, and SHA-256 hashes of the Python and Lean sources. Floating values sit in a separate informational section and are excluded from that gate. The default Lean path supports this scratch directory and the planned MathCan layout; `--lean-source PATH` selects an explicit file.

## Countermodel: charge matching

Let H_A=H_B=ell^2(Z), with Q_A|n>=n|n> and Q_B|n>=n|n>. The kernel of Q_A tensor I + I tensor Q_B contains the orthonormal set |n> tensor |-n> for every integer n. Its dimension is countably infinite.

Restricting each charge to [-M,M] gives ambient dimension (2M+1)^2 and physical dimension 2M+1. The compression ratio grows with M while the physical dimension also grows without bound. A finite-alphabet graph gym tests exact constrained compression at a specified cutoff. Extrapolation needs an independent bound that survives removal of that cutoff.

## Countermodel: matrix elements and closed sewing

Take H=ell^2(N), U=I and any square-summable input vectors a,b. Cauchy-Schwarz proves sum_n |conj(a_n)b_n| <= ||a|| ||b||. The closed identity has Tr(I)=infinity.

For a bounded C, a finite-cut sewing vector is

    Psi_P = sum_(i in P) C e_i tensor conjugate(e_i).

Its squared norm is Tr(P C* C). If C* C >= m I, this norm is at least m rank(P). Consequently the vectors grow without a finite norm bound as the cut includes more states. A rule that closes every such cut into a finite amplitude therefore adds information beyond the bound on matrix elements.

## Diagnostic: strong exhaustion and normalized cutoff order

On ell^2(N_0), let S e_n=0 for even n and S e_n=log(2)e_n for odd n. Then W=exp(-S) has weights 1 on even indices and 1/2 on odd indices. Its spectrum lies in [1/2,1], and its ordinary trace is infinite. Let E project onto the even indices.

Fix an integer r>=2. The kth cycle contains r-1 even indices

    2((r-1)k), 2((r-1)k+1), ..., 2((r-1)k+r-2)

and the odd index 2k+1. Let P_(K,r) project onto the first K complete cycles. The rank is rK. Every index below 2K is included, so for each fixed r these projections converge strongly to the identity. This follows first for finite-support vectors and then for every vector by density and ||P_(K,r)||<=1.

The normalized expectation of E is exact at every K>=1:

    Tr(P_(K,r) W E) / Tr(P_(K,r) W)
      = K(r-1) / [K(r-1)+K/2]
      = 2(r-1)/(2r-1).

For r=2,3,5,17, the values are 2/3,4/5,8/9,32/33. Each sequence gives a constant finite-cutoff ratio while exhausting the same basis. Strong exhaustion alone therefore leaves a normalized trace limit undetermined. The weights, bounded area, and observable remain fixed throughout this example.

The script checks uniqueness and coverage of the selected indices together with the exact ratios. It records the growing unnormalized weight as well. This diagnoses an inference about cutoff limits; it does not settle a gravitational gluing rule. An independent finite-trace theorem would remove the freedom displayed here.

## Lean finite-sum proof

`NullConeTraceBound.lean` imports only `Std` and defines the natural-number sum `partialWeight w n`. It proves n*m <= partialWeight w n from a uniform lower bound m<=w_i, then obtains n<=Z from a total budget and m>=1. Applying this statement to n=Z+1 rules out a uniform finite budget for an infinite list of positive scaled weights.

The file contains `#print axioms` commands for each theorem. It uses no admitted goals and no native evaluator. Its scope is scaled integer weights and finite sums. The analytic Hilbert-space argument above remains a prose proof.

Local validation passed with official Lean 4.35.0, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, exit code 0. Each theorem reports `[propext, Quot.sound]` in its axiom inventory; `sorryAx` is absent. `lean_validation.log` and `lean_validation.json` record the result and source hash. The compiler archive matched the official release SHA-256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` before extraction.

## Proof obligations to isolate

1. Specify the completed observable algebra and demonstrate that the chosen pure extension has the required continuity for its one-parameter groups. Algebraic unitarity by itself establishes an isometry, while a self-adjoint generator needs strong continuity.
2. Give domains and closed forms for nonlinear field products and exponentials. Show how the nonnegative shear prescription, the clock spectral projection, and the source derivatives act on a common domain after removing regulators.
3. State the closed-sewing convergence condition used for finite-rank nets. Track the topology under which it identifies the cut amplitude with a finite, nonzero uncut amplitude. A proof about vector matrix elements alone leaves this condition open.
4. Bound the remainder that transfers a perturbative boost response into the exact state selected by the full algebra. The sign argument needs the remainder below its stated positive margin, including contributions outside the chosen smooth saddle family.
5. Convert the quadratic focusing estimate into a spectral counting theorem with controlled zero modes and boundary conditions. Record where the regulator enters the constants before inferring a limit.

These are requests for a stronger proof audit. They do not establish that the proposed theory is inconsistent.

## Retrieval locations for review

All locations use the source URL above. Web extraction lines are internal navigation aids, not publication page numbers.

| Topic | Equations or section | Extracted lines |
| --- | --- | --- |
| Pure extension and GNS | 4.16-4.18 | 788-800 |
| Choice of representation | footnote 20 | 1220 |
| Single-cut convergence | 4.29-4.30 | 851-859 |
| Positive nonlinear shear and clock | 4.22-4.26 | 819-836 |
| Area bound | 5.21 | 1227-1232 |
| Uniform positive lower bound | 5.30 | 1272-1275 |
| Finite-cut vectors and phase bound | 5.31-5.32; D.22-D.25 | 1276-1280; 2008-2023 |
| Signed gluing argument | 5.37-5.38 | 1295-1307 |
| Quadratic mode counting | D.39-D.46 | 2071-2104 |
| Replica-ratio check | D.47-D.49 | 2105-2117 |
| Finite closed amplitudes axiom | E.1 condition 5 | 2170-2177 |
| Dependency on finite dimension | E.17 | 2229-2232 |
