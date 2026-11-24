# Candidate theorem: a sharp Euclidean rank-observer bound

Original derivation for VPVNP-02. Proof draft, pending independent review and Lean certification.

Let V=Mat_n(F2), n>=2, with pairing <B,W>=sum_ij B_ij W_ij mod 2 and characters chi_B(W)=(-1)^<B,W>. Put p_r(k)=Pr[<B,W>=1 | rank W=r], where rank B=k. Under W -> L W R, dual B transforms by inverse transposes; hence p_r depends only on k. For a Euclidean vector map f, use normalized Walsh coefficients h_B=E_A f(A)chi_B(A). Parseval applied to f(A+W)-f(A) gives

D_f(r)^2 = 4 sum_{B!=0} ||h_B||^2 p_r(rank B).

For rank one, W=u v^T with u,v independently uniform nonzero (unique over F2). For a rank-k B, 2^n-2^(n-k) nonzero u have B^T u != 0; for each such u exactly 2^(n-1) nonzero v have pairing one. Thus

p_1(k) = (2^n-2^(n-k)) 2^(n-1)/(2^n-1)^2.

For full rank use the kernel lattice of W. The indicator of ker W=0 equals sum_{U <= ker W} mu(0,U), where the subspace-lattice Mobius value for dim U=d is (-1)^d 2^(d(d-1)/2). The character sum over W vanishing on U is 2^(n(n-d)) if every row of B belongs to U (orthogonal complement of the linear subspace of W with U in its kernel), and zero otherwise. Writing k=rank B and [a b]_2 for the Gaussian binomial coefficient gives

sum_{W invertible} chi_B(W)
= sum_{d=k}^n [n-k d-k]_2 (-1)^d 2^(d(d-1)/2+n(n-d)).

Apply the finite q-binomial theorem with q=2 and z=-2^(k-n). Dividing by |GL(n,2)|=2^(n^2) prod_{i=1}^n (1-2^(-i)) yields

E_{W invertible} chi_B(W) = (-1)^k / prod_{i=n-k+1}^n (2^i-1).

Hence p_n(k)=(1-E chi_B)/2. For k>=1, p_1(k)>=p_1(1)>0, while p_n(k)<= (1+1/(2^n-1))/2=p_n(1), since the denominator product is at least 2^n-1. The exact extremal squared ratio is therefore

D_f(n)^2 / D_f(1)^2 <= p_n(1)/p_1(1) = 2(1-2^(-n)) < n.

Equality in the first inequality is attained by a scalar rank-one Walsh character; the constant map has both D's zero. For any nonconstant Euclidean f the ratio is a convex combination with weights proportional to ||h_B||^2 p_1(rank B). This proof uses the uniform basepoint A and exact F2 rank strata. The inequality is a universal feature of the observer restriction, independent of how f was produced. It is not the upstream price dichotomy: the upstream price geometry quantifies over a different class, including finite Euclidean configurations in the flat case. Restricting the domain to matrix rank-stratified observers also says nothing about arithmetic circuit size. Future comparisons must account for this sharp null before attributing contraction to learning.
