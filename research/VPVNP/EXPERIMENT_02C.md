# VPVNP-02C: actual Walsh basis and ordered-basis character recurrence

Registered 2026-11-24, before the new exact basis-DP evaluation. Source: the MathCan 02B proof and Anthropic's rank-conditioned distance in Paper/Alternative.lean. This is independent mathematics; the upstream proof did not supply these binary-observer lemmas.

## C1: actual Walsh basis

For any finite coordinate set I, A=I -> ZMod 2. Pairing is sum_i b_i a_i in ZMod 2; the character is +1 at parity zero and -1 at parity one. For b!=0, translate a by the coordinate unit vector at a nonzero component of b. The sum of the character over A equals its negative, hence vanishes. For b=0 the sum is |A|. Since chi_b chi_c=chi_(b+c), this proves orthogonality. Symmetry of the pairing also gives the dual orthogonality and the inverse Walsh expansion for every scalar observer. Finite coordinate sets include Fin n × Fin n, with no need to treat the matrix as a free hypothesis. C1 requires native proofs, with no assumed orthogonality or reconstruction, and an axiom receipt. Vector observables follow coordinatewise; the vector shift-average and rank-specific character counts are separate obligations.

## C2: elementary recurrence for the invertible character sum

Write F(n,k) = E_{W in GL(n,2)} (-1)^(sum_{i=1}^k W_ii). Permuting columns and rows or changing bases preserves the distribution, so choose the nonzero diagonal positions to include the final column, with k-1 of the other columns paired with the first k-1 coordinates. Invariant formulation: the column coefficient functionals are k independent nonzero functionals, others zero.

Sample an ordered basis by first taking n-1 independent vectors and then a final vector outside their span H, a hyperplane. All hyperplanes occur equally often because GL(n,2) acts transitively on them and each has the same number of ordered bases. There are 2^n-1 hyperplanes (each is the kernel of a unique nonzero binary functional). Let the final column coefficient be the nonzero functional L.

- If H != ker L, L restricts nontrivially to H. Both H and its complementary coset are balanced under L, by translation by a vector in H on which L is 1. The conditional final-column character average is zero.
- If H = ker L, all vectors outside H have L=1, so the average is -1. The remaining columns form a uniform basis of H. The other k-1 functionals remain independent after restriction to H: a vanishing linear combination on H would be a multiple of L, contradicting the original independence.

Therefore F(n,0)=1 and F(n,k)=-F(n-1,k-1)/(2^n-1) for 1<=k<=n. Iteration gives (-1)^k / product_{i=n-k+1}^n (2^i-1). This proof replaces the subspace-lattice Mobius/q-binomial step in the first draft. It is a mathematical proof draft pending review and formalization; Lean C1 alone does not certify the matrix count.

## C3: exact regression and acceptance

Independent ordered-basis DP: state is the actual span as a bitset of F2^n, value is the signed integer count of all partial ordered bases with that span. Extend by every vector outside the span, update sign by the prescribed column functional, and merge equal spans. No enumeration of all matrices and no use of the recurrence in the DP. Run all dual ranks 0..n at n=1..6, including 6x6. Compare signed counts divided by independently computed |GL(n,2)| against the formula and recurrence. Also enumerate nonzero outer products u v^T for every n,k in the same range, check the rank-one probabilities, and compare the overlapping n=2,3,4 counts to the frozen 02A archive. All comparisons exact, no sampling. Record runtime and states optionally outside the deterministic JSON. No tuning.

C4 next: formalize the uniform hyperplane partition, fiber cardinalities and balanced final coset, then derive the recurrence for actual invertible matrices. Compose with the C1 and B mixture proofs and discharge all rank-bound assumptions before making an all-n kernel-certified claim.
