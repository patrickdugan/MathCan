# CLN-01 — Prefix entropy, modular orbits and Liouville normality

2026-11-24. Research derivation from the user-supplied three-page note
"Binary-normal Liouville numbers in the middle-third Cantor set".
The author's identity and publication priority were not supplied. Credit
the original tail-conditioning/Fourier argument to that manuscript.
The extensions below are a working mathematical derivation, not a
claim of priority or a fully kernel-checked theorem.

## 1. General theorem

Let Q >= 2 be an integer source base, X = A_k/Q^k + T_k, and A_k
take values in {0,...,Q^k-1}. Write alpha_k for a deterministic upper
bound on the largest conditional probability of A_k given T_k
(almost surely). Suppose sum_{k>=1} alpha_k < infinity.
Then X is almost surely normal to every integer base b >= 2 with
gcd(b,Q)=1. X may be reduced modulo one without changing the assertion.

For independent fair choices between two different base-Q digits at
positions F, and deterministic digits elsewhere, alpha_k = 2^(-s(k)),
where s(k)=#(F intersect [1,k]). Thus s(k) >= (1+epsilon)log_2(k)
eventually suffices. More generally, use independent nonuniform digits
and bound the product of their maximum probabilities. This theorem
uses conditional min-entropy, allowing some dependent digit models.
An unconditional maximum prefix probability is insufficient for the
conditioning proof unless the conditional bound is established.

## 2. Uniform-in-tail Fourier estimate

Fix b coprime to Q and nonzero integer h. Let e(t)=exp(2*pi*i*t),
N>=Q, k=floor(log_Q N), M=Q^k,
W_N=(1/N)sum_{0<=n<N} e(h*b^n*X).
Given the tail T, let w_n=e(h*b^n*T). Nonnegativity and finite
orthogonality give

    E[|W_N|^2 | T]
    <= alpha_k/N^2 sum_{a=0}^{M-1} |sum_n w_n e(h*b^n*a/M)|^2
    = alpha_k M/N^2 sum_{n,m: h*b^n=h*b^m (mod M)} w_n conj(w_m)
    <= alpha_k M/N^2 C(N,P),

where D=M/gcd(M,|h|) and P=ord_D(b), with order modulo 1 defined as 1.
Cancellation of h followed by cancellation of the unit b^min(n,m)
makes the collision condition exactly n=m (mod P).

Writing N=uP+r, 0<=r<P, the exact ordered collision count is

    C(N,P) = P*u^2 + r*(2*u+1) <= N*(1+N/P).

Indeed each residue class contains u or u+1 indices, and summing
the squares counts ordered pairs. Equality in the complex-energy
bound is possible with aligned phases within each fiber. No estimate
on T or phase cancellation is needed.

## 3. Period lower bound for arbitrary composite Q

Factor Q=product_{p|Q} p^e_p. Set v_p=v_p(|h|).
For odd p choose d_p=p-1; for p=2 choose d_2=2.
Since b is a unit at p, c_p=v_p(b^d_p-1) is finite and >=1
(>=3 when p=2). For all r>=0,

    v_p((b^d_p)^(p^r)-1) = c_p+r.

Proof: write z=1+p^c u with p not dividing u and expand z^p-1.
The first term has valuation c+1; the other terms have strictly
higher valuation for odd p or for p=2 with c>=2. The same binomial
argument for raising to an exponent coprime to p preserves valuation.
Therefore the order of b^d_p modulo p^t is p^max(t-c_p,0).

D contains p^t with t=max(e_p*k-v_p,0). Each such p-power order
divides P since (b^d_p)^P=1 modulo p^t. Their product divides P,
as the factors are powers of distinct primes. Consequently

    M/P <= K(b,Q,h) := product_{p|Q} p^(v_p+c_p).

For Q=3, a sharper constant follows by taking
d=ord_3(b), c=v_3(b^d-1), and ord_{3^t}(b)=d*3^(t-c)
for t>=c. With b=2, d=2, c=1, recovering the source's constant
1+3^(v_3(h)+1)/2.

Combining M<=N and M/P<=K gives the bound

    E|W_N|^2 <= (1+K) alpha_k.

## 4. Elementary interpolation (no DEL theorem required)

For each fixed positive integer J use the grid

    N_{k,j}=Q^k+floor(j*Q^k/J), 0<=j<(Q-1)J.

All grid sizes lie in [Q^k,Q^(k+1)), and the number per k is fixed.
The sum of E|W_{N_{k,j}}|^2 over k,j is finite. By monotone
convergence the sum of squared Weyl averages on that grid is finite
almost surely; hence their maximum over j tends to zero as k grows.
For an arbitrary N in the block, choose the largest grid size N0<=N.
The next gap (including the terminal endpoint) is at most Q^k/J+1.

    |W_N| <= |W_{N0}| + (N-N0)/N0
           <= |W_{N0}| + 1/J + Q^(-k).

Intersect the probability-one events for every J, nonzero h and
coprime base b, all countable. Let J tend to infinity and apply
Weyl's criterion. For irrational X, the orbit b^n X mod 1 lies in
the interval corresponding to a base-b word of length d exactly when
that word starts at position n+1. Uniform distribution yields frequency
b^(-d) for every word. Uniform distribution itself excludes rational X.

Alternative analytic reference: the Davenport–Erdos–LeVeque summability
criterion also applies, since summing 1/N over each Q-adic block is
bounded uniformly in k. The grid proof makes the interpolation explicit.

## 5. Stronger Liouville corollary and excluded bases

For every integer Q>=2, choose free digits {0,Q-1} on disjoint blocks
[m_j,2m_j], and zero elsewhere. One can retain the supplied manuscript's
m_1=256, m_{j+1}=2^ceil(sqrt(m_j)). Alternatively take the much larger
integer schedule m_{j+1}=2^floor(m_j/2).

For the second schedule m_{j+1}/m_j tends to infinity and, for
2m_j<=k<2m_{j+1}, s(k)>=m_j and log_2(k)<1+floor(m_j/2).
Hence s(k)>2log_2(k)-2, and sum_k 2^(-s(k)) converges.
The faster schedule is optional; it does not strengthen the
normality conclusion, but permits substantially longer zero gaps.

Let L_j=2m_j, p_j/Q^L_j be the truncation, and R_j=m_{j+1}.
Almost surely infinitely many nonzero digits occur, giving

    0 < X-p_j/Q^L_j <= Q^(1-R_j).

This error is below (Q^L_j)^(-A) for every fixed A>0 eventually.
A rational a/c distinct from the truncation would differ by at least
1/(c Q^L_j), so X is irrational; reduction of denominators preserves
the approximation inequality and their reduced denominators are
unbounded. X is Liouville almost surely.

Now take b with rad(Q) dividing rad(b), i.e. every prime of Q divides b.
Set

    t_j = max_{p|Q} ceil(e_p L_j/v_p(b)),
    U_j = floor((R_j-2) log(Q)/(2 log(b))).

For t_j<=n<=U_j, b^n*p_j/Q^L_j is an integer, while

    0 <= b^n*(X-p_j/Q^L_j)
       <= b^U_j * Q^(1-R_j) <= Q^(-R_j/2).

For sufficiently large j this is less than 1/b, so the base-b digit
at position n+1 is zero. Since t_j=O(L_j), U_j grows proportionally
to R_j and L_j/R_j -> 0, the proportion of zero digits among the
first U_j+1 positions tends to 1 along this subsequence.
Thus X fails even simple normality in every such b, for every
realization with the indicated forced zero gaps. For composite Q and
bases sharing only some prime factors, this argument makes no claim.

For Q=3 the two base classes exhaust the integer bases >=2.
Almost surely X is in the middle-third Cantor set, is Liouville,
is normal in precisely the bases coprime to 3, and is not simply
normal in any multiple of 3. The digit measure is non-atomic:
admissible prefix masses tend to zero, and at most two digit
expansions represent a given real number. Consequently the full
measure intersection is uncountable. Its Hausdorff dimension is
zero (Liouville numbers have dimension zero).

## 6. Referee and provenance

The supplied note's three main steps pass the written proof audit.
The extension to composite Q, conditional min-entropy, a sharper
summability hypothesis and the elementary grid argument are derived
here. The original Bugeaud question is its ternary/binary corollary.
No claim is made that these extensions are new in the literature.

- Y. Bugeaud, Distribution Modulo One and Diophantine Approximation
  (Cambridge, 2012), Problem 10.37, p. 220.
- V. Becher and S. Lew Deveali, Normal numbers in sparse Cantor sets,
  arXiv:2607.06773 (2026), https://arxiv.org/abs/2607.06773.
  Their abstract states a local logarithmic count condition for
  sparse binary digit sets and full measure normality in all odd
  bases, as well as an effective construction. The hypothesis and
  conclusion here should be compared against the full paper before
  asserting any novelty.
- H. Davenport, P. Erdos and W. J. LeVeque, On Weyl's criterion for
  uniform distribution, Michigan Math. J. 10 (1963), 311–314,
  https://www.renyi.hu/~p_erdos/1963-13.pdf.
- For the general probability-measure version of DEL see
  https://academic.oup.com/imrn/article/2022/16/12378/6246797,
  Proposition 3.1.

## 7. Formalization boundary

The core MathCan Lean module addresses quotient/remainder injectivity,
a generic collision-bound assembly and finite first-return examples.
It does not formalize complex Fourier orthogonality, the general
prime-power order theorem, probability or real normality.

Next gate: separate Mathlib-enabled project pinned to a compatible
Lean/Mathlib revision, with explicit dependency chain:
  1. ZMod cancellation and first-return iff period divides index gap;
  2. exact fiber counts, finite complex Fourier orthogonality;
  3. p-adic valuation and order growth, including the 2-adic case;
  4. conditional prefix max-mass bound, product-digit independence;
  5. integrable Weyl averages, monotone convergence, countable a.e.
     intersections, grid interpolation and Weyl criterion;
  6. digit-word equivalence and Liouville approximation, including the
     excluded bases and non-atomicity.

Require no sorry, no added axioms, theorem-statement review and
#print axioms on each exported target; finite numerical oracles are
regressions, not proofs of the asymptotic theorem.
