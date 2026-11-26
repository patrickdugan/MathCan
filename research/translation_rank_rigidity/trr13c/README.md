# TRR-13C: independent audit of Mythos's sparse-edit rigidity review

Date: 2026-11-26. Scope: finite cyclic functions, root counts and
restricted representation lower bounds. The uploaded verify.js is
preserved as supplied. Local Node.js v22.16.0 default replay:
56 checks passed, 0 failed; 1,082 (p,N) cohorts and 138 distinct
prime orders in the default k=1 sweep. The full mode is not yet
independently executed at publication. It is a separate CI job.

Original SHA-256:
1edae6f84507afa571dbb617fca68eb1a993e659a95412dad7c631290caaf109
Git blob: d918d03c6a235e5e5441bf66eff8663254c585f0.

## 1. Exact equality classification (written proof review)

For an odd cyclic order N, in a field of characteristic not
dividing N, let Z be a fibre of z^i(z-1)=lambda!=0 on mu_N,
0<=i<N. The ratio argument gives m(m-1)<=N-1. Equality
means every nonidentity ratio occurs exactly once. Hence Z
is a cyclic (N,m,1) difference set. This is equality in the
quadratic inequality, distinct from attaining its rounded
integer upper bound.

Let n=m-1. For n>=2 and every prime ell|n, Hall's multiplier
theorem for lambda=1 applies (gcd(ell,N)=1 because
N=n^2+n+1). It yields Z^ell=gZ for some g in mu_N.
Combining the two fibre equations gives
z^ell-g=kappa*(z-1)^ell at every z in Z, with kappa!=0.
The polynomial difference has degree <=ell<=n<m, so
it vanishes identically. Leading coefficients give kappa=1,
and the coefficient of X^(ell-1) forces ell=0 in K.
Thus characteristic is p and n=p^e. This also excludes
characteristic zero. Reference: Schmidt's survey of multiplier
theorems, Result 1.1:
https://www3.ntu.edu.sg/home/Bernhard/Publications/pub/Multiplier_Survey.pdf

Let S_j=sum_{z in Z}z^j. The difference-set equation gives
S_0=1 and S_j*S_-j=0 for j nonzero modulo N, and
S_{j+i+1}-S_{j+i}=lambda*S_j.
The endpoint i=0 or N-1 is injective, so exclude it.
S_i and S_{i+1} cannot both be nonzero: the corresponding
negative-index sums would vanish, and the recurrence at
j=-i,-i-1 would give S_1=S_-1=1. Inversion switches i to
N-1-i and lambda to -lambda. Assume S_i=0.
Then S_{i+1}=lambda, S_-1=1 and S_1=0.
For J=N-1-i, induction for 1<=k<=J gives
S_k=0, S_-k=1 and S_{i+k}=lambda: the forward recurrence
at j=k gives S_{i+k+1}=lambda; its negative-index partner
vanishes, giving S_-(k+1)=S_-k via j=-i-k-1; multiply
S_{k+1} by S_-(k+1). The induction uses only nonzero indices
modulo N. At k=J obtain lambda=1. The fibre equation
becomes z^(J+1)=z-1. Root count implies J>=n.
If J>=n+1 then Newton's identity at m=n+1 would force
m*e_m=0 although e_m is the nonzero product of roots and
m=1 in K. So J=n and i=n^2. From z^(n+1)=z-1 and
n=p^e follows z^(n^2+n)=z^n-1, hence z^N=-1; since z^N=1,
p=2. Inverting yields i=n. In characteristic two lambda=1
corresponds to c=1. For N=3, equality requires i=1 and
both nonidentity roots. Their sum is -1; the quadratic
X^2-X-lambda has root sum 1, forcing characteristic 2
and lambda=c=1. This is the e=0 endpoint.

Conversely q=2^e, N=q^2+q+1: every root of
X^(q+1)+X+1 satisfies z^N=1, using z^q+1=z^(q^2+q)
and z^(q+1)+z=1. The polynomial is squarefree: for q>1
its derivative is X^q+1, and at a common root z^q=1
would make the original polynomial equal 1. The q=1 case
is the direct quadratic. On mu_N it is equivalent to
1+z^(q^2)(z+1)=0. Inversion supplies i=q. Thus m=q+1.
This verifies the equality classification and extends it
from prime N to every odd cyclic order with N nonzero in K.
It supplies unconditional infinitely many sharp composite
or prime orders together; infinite prime orders are open.
For e>0, write e=3^a*b, 3 not dividing b. Then
Phi_3(2^(3^a)) divides Phi_3(2^e), so primality requires b=1.
The original verifier certifies composite e=3^a for
a=3,...,9, and exact gcd equality at e=1,3,9.
The finite list does not establish infinitude.

## 2. Index-seven section formula: complete derivation

Let q=2^e and 3 not dividing e. M=q^2+q+1 is divisible by 7
and q-1 is coprime to 7. Put U=M/7. Identify
F_(q^3)^*/F_q^* with mu_M by z=y^(q-1). The trace-zero
projective points form the set Z defined by
1+z+z^(q+1)=0, since Tr(y)/y=1+z+z^(q+1).
Its inverse set is defined by 1+z^q+z^(q+1)=0.
Thus the supplied cofactor-seven gcd counts the intersection
with the unique subgroup of index 7 in the quotient.

For nontrivial order-seven multiplicative character chi on
F_(q^3)^*, trivial on F_q^*, let
S(chi)=sum_{[y]:Tr(y)=0}chi(y).
Let psi(y)=(-1)^Tr_(q^3/2)(y). Trace orthogonality gives

 S(chi) = (1/(q*(q-1))) sum_{a in F_q} sum_{y!=0} chi(y)psi(ay)
        = G_(q^3)(chi)/q.

The a=0 term vanishes; every other term equals the Gauss
sum because chi(a)=1. All six chi are norm lifts of
nontrivial multiplicative characters chi0 of F_8^*
to F_(8^e)^*. By Davenport-Hasse lifting,
G_(8^e)(chi)=(-1)^(e-1)*G_8(chi0)^e.
Reference: Handbook of Finite Fields, theorem 6.1.45,
https://studylib.net/doc/27983195/handbook-of-finite-field

In F_8 choose a primitive root alpha of X^3+X+1; its
three nonzero trace-zero elements have exponents 1,2,4.
For zeta primitive complex seventh root, eta=zeta+zeta^2+zeta^4.
The complement exponents are 3,5,6, so eta+eta_bar=-1.
The six ordered nontrivial differences among 1,2,4 exhaust
1,...,6; consequently eta*eta_bar=2.
The base Gauss sums are 2*eta and 2*eta_bar, three copies
of each, because the character sum of all nonzero elements
is zero and psi is +1 exactly on the trace-zero elements.
After division by q=2^e the six values of S(chi) are
three copies each of (-1)^(e-1)*eta^e and its conjugate.
Index-seven character orthogonality now gives

 7m=q+1+3*(-1)^(e-1)*V_e,
 V_0=2, V_1=-1, V_(e+1)=-V_e-2V_(e-1).

In particular m=q/7+O(sqrt(q))=sqrt(U/7)+O(U^(1/4)).
No primality assumption is needed for the count. The
larger e=23,31 rows are exact deductions from the
Gauss-sum formula and independently checked Lucas
primality certificates, not direct polynomial gcd runs.
e=11 is directly replayed in the uploaded verifier.

More generally for an index h subgroup of the Singer
difference set's ambient group, orthogonality and the
nontrivial character magnitude sqrt(q) yield
|h*m-(q+1)|<=(h-1)*sqrt(q), including composite indices.

## 3. Two-edit bound (written proof review)

Let N be prime, i1 and i2 distinct modulo N, coefficients
nonzero. For distinct s,t!=1, every triple w,sw,tw of roots
makes the three-by-three matrix with rows
((sigma*w-1)*sigma^i1,(sigma*w-1)*sigma^i2,1),
sigma in {1,s,t}, singular. The determinant has degree <=2.
At w=t^-1 its value, up to sign, is
(t^-1-1)*(s*t^-1-1)*(s^i2-s^i1), nonzero by primality and
the distinct exponents. Hence at most two w for fixed s,t.
In fact prime N can be relaxed to gcd(i2-i1,N)=1.

Let tau(s,t)=#{w:w,sw,tw in Z} and r(s)=#{w:w,sw in Z}.
Counting triples yields
(m)_3 = sum_{s,t distinct nonidentity} tau(s,t)
       <= 2*(N-1)*(N-2).
Counting ordered triples in the intersections indexed by s
gives sum_s (r(s))_3 = sum_{a,b distinct nonidentity}
tau(a,b)*(tau(a,b)-1) <= (m)_3, since tau<=2.
Here (x)_3=x*(x-1)*(x-2). Its values on nonnegative integers
form a convex sequence (including x=0,1,2); use piecewise
linear interpolation in Jensen, which dominates the cubic
on [1,infinity). With rho=m*(m-1)/(N-1)>=2,
(N-1)*rho*(rho-1)*(rho-2)<=(m)_3. Divide to get
(rho-1)*(rho-2)<=m-2; for rho<2 the displayed upper bound
rho<=(3+sqrt(4m-7))/2 holds automatically when m>=2.

For t=N^(1/3)>1, at m0=t^2+t+1,
m0*(m0-1)/(N-1)=(t^2+t)/(t-1)>t+2,
while (3+sqrt(4m0-7))/2<t+2.
The ratio m*(m-1)/(3/2+sqrt(m-7/4)) is strictly
increasing for m>=2 (differentiate, or compare the
relative growth of numerator and denominator). Thus
m>=m0 is impossible. This proves m<N^(2/3)+N^(1/3)+1,
improving the leading constant 3 of TRR-13B to 1.
The exact integer cap retains both inequalities.
The upper bound is a representation result; the leading
exponent's optimality is open. General k>=3 needs control
of determinant degeneracy; the prior dilation bound remains valid.

## 4. Additional qualifications and scope

- In characteristic zero f_i is actually injective on
  nonidentity Nth roots for odd N: equal magnitude of
  z-1 forces w=z or z^-1; the latter equality would require
  z^(2i+1)=-1, impossible for odd N. Chebotarev's theorem
  gives the broader m<=2k for k edits.
- For p^d>=3^(N-1) and prime N>=5 (d=ord_N(p)), the
  singleton assertion has a direct norm proof. A collision
  would reduce a nonzero cyclotomic integer D, a sum of
  two positive and two negative roots of unity, to zero
  modulo a prime of norm p^d. In complex characteristic
  zero D!=0 by injectivity. Reduce its exponents modulo N.
  If the sum of coefficient squares <=6, Parseval and
  AM-GM give |Norm D|<3^(N-1), since D(1)=0 and
  6N/(N-1)<9. The only remaining case is D=2*(zeta^a-
  zeta^b) up to sign; its norm is 2^(N-1)*N<3^(N-1)
  for N>=5. This contradicts divisibility by p^d.
- For c in F_p^*, roots split into Frobenius orbits of
  length d, so d|m. If p=2 is primitive modulo prime
  N>=5 and arbitrary c is allowed, a collision yields
  a binary polynomial of degree <N with at most four terms;
  irreducibility of Phi_N forces it to be identically zero,
  hence exponents pair across the two roots. This forces
  w=z^-1 and 2i+1=0 modulo N; the mirror pair really
  collides in characteristic 2. Thus max m=2. This
  is about arbitrary extension coefficients; for c=1
  there are no roots in that primitive-root regime.
- The list of Mersenne examples certifies exhibited gcd
  degrees; default code does not exhaust all exponents
  for the large Mersenne primes. Growth on an infinite
  family of prime orders is not established. The odd
  characteristic PG(4,q) fibre sizes are observed controls,
  not a uniform theorem in the supplied proof.
- The exact binary cofactor and single-edit results concern
  synthetic cyclic labels. They imply sharp limitations of
  finite-field translation-rank bounds, not a new recovery
  mechanism or an unrestricted computational lower bound.
  TRR-12's shared-circuit scope control remains mandatory.

## 5. Verification boundary

Default original replay: 56 passed, 0 failed. Exact gcd
certificates, extension-field evaluation, the supplied
maxima through N=31, and its stated finite search cohorts
were exercised. The independently written audit script
checks base Gaussian periods, cofactor arithmetic and
Lucas certificates, modest binary gcds and the exact
two-edit cap. Neither the full 1,706-pair sweep nor the
exhaustive k=2 maximum at N=257 was independently replayed
before publication; the explicit N=257 witness with 24
roots was checked in default mode. The original code is
retained unchanged; CI also runs a hardened copy requiring
successful field construction, safe counters and triangular
pair counts. The new mathematical results have written proofs
with classical literature dependencies; they are not yet Lean-checked.
