"""ROC-01 exact rational counterexamples and finite-horizon geometry.

Standard-library Fraction computations, matrices d<=6. This checks stated
identities and constructed witnesses; full real-matrix theorem proofs remain
in PART2_THEORY.md and have a separate Lean scope ledger.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations


def rat(X):
    return [[F(v) for v in row] for row in X]


def transpose(X):
    return [list(x) for x in zip(*X)]


def mul(A,B):
    if len(A[0])!=len(B):
        raise ValueError("Dimension mismatch")
    return [[sum((a*b for a,b in zip(row,col)),F(0)) for col in transpose(B)]
            for row in A]


def zeros(d,k):
    return [[F(0)]*k for _ in range(d)]


def eye(d):
    return [[F(i==j) for j in range(d)] for i in range(d)]


def minus(A,B):
    return [[a-b for a,b in zip(u,v)] for u,v in zip(A,B)]


def fnorm2(A):
    return sum((x*x for row in A for x in row),F(0))


def rank(X):
    M=rat(X)
    n,m=len(M),len(M[0])
    r=0
    for j in range(m):
        pivot=next((i for i in range(r,n) if M[i][j]!=0),None)
        if pivot is None:
            continue
        M[r],M[pivot]=M[pivot],M[r]
        div=M[r][j]
        M[r]=[x/div for x in M[r]]
        for i in range(n):
            if i!=r:
                w=M[i][j]
                M[i]=[x-w*y for x,y in zip(M[i],M[r])]
        r+=1
        if r==n:
            break
    return r


def observable(T,G,N):
    d=len(T)
    if not N>=1 or len(T[0])!=d or len(G[0])!=d:
        raise ValueError("Valid time horizon and square transition")
    blocks=[]
    A=eye(d)
    for _ in range(N):
        blocks.extend(mul(G,A))
        A=mul(A,T)
    return blocks


def closure_rank(T,G):
    return rank(observable(T,G,len(T)))


def exact_energy_bound(T,G,U,Q,horizon):
    """Rational upper bound for observable leakage, without a floating SVD.

    E=U^T(T-I)Q. Under GQ=0 and U^TQ=0,
    ||O_N Q||F^2 <= ||G||F^2 ||E||F^2 Σ_{j=1}^{N-1} j²||T||F^{2(j-1)}.
    """
    d=len(T)
    if horizon<1 or len(U)!=d or len(Q)!=d:
        raise ValueError("Invalid state dimension or horizon")
    if mul(transpose(U),Q)!=zeros(len(U[0]),len(Q[0])) or mul(G,Q)!=zeros(len(G),len(Q[0])):
        raise ValueError("The readout must lie inside U, and U must be perpendicular to Q")
    B=mul(mul(transpose(U),minus(T,eye(d))),Q)
    OQ=mul(observable(T,G,horizon),Q)
    M2=fnorm2(T)
    factor=fnorm2(G)*sum((F(j*j)*M2**(j-1)
                        for j in range(1,horizon)),F(0))
    lhs=fnorm2(OQ)
    rhs=factor*fnorm2(B)
    return {"lhs":lhs,"rhs":rhs,"holds":lhs<=rhs,"B2":fnorm2(B)}


def rank_one_four_codes():
    pts=((0,0),(1,0),(0,1),(1,1))
    codes=[F(x+2*y) for x,y in pts]
    return {"points":pts,"codes":codes,"distinct":len(set(codes))==4}


def no_rank2_extension_rotation():
    """The four test vectors check the claimed real rotation counterexample."""
    T=rat([[1,0,0],[0,0,-1],[0,1,0]])
    G=rat([[1,0,0]])
    witnesses=[]
    for a,b in ((1,0),(0,1),(F(3,5),F(4,5)),(F(5,13),F(12,13))):
        U=rat([[1,0],[0,a],[0,b]])
        Q=rat([[0],[-b],[a]])
        B=mul(mul(transpose(U),minus(T,eye(3))),Q)
        witnesses.append({"v":[a,b],"B2":fnorm2(B)})
    return {"T":T,"G":G,"closure_rank":closure_rank(T,G),
            "rank2_witnesses":witnesses,
            "all_B2_eq_one":all(x["B2"]==1 for x in witnesses)}


def min_separating_arm_set(signatures):
    """Finite nonadaptive pair-cover, as in EvalMath BPD-01 T1."""
    names=list(signatures)
    arms=list(next(iter(signatures.values())))
    for k in range(len(arms)+1):
        for ids in combinations(arms,k):
            if all(any(signatures[a][e]!=signatures[b][e] for e in ids)
                   for a,b in combinations(names,2)):
                return ids
    return None


# Idealization ONLY: tags can overlap in genuine linear dynamics. This
# canonical five-row signature is a hypothesis table, not a neural receipt.
IDEAL_SIGNATURES={
 "closed_quotient":{"dark_to_observed":0,"observed_to_dark":1,
                    "observed_to_observed":1,"ablate_readout":1},
 "invariant_subspace":{"dark_to_observed":1,"observed_to_dark":0,
                     "observed_to_observed":1,"ablate_readout":1},
 "latched_memory":{"dark_to_observed":0,"observed_to_dark":1,
                   "observed_to_observed":0,"ablate_readout":1},
 "output_register":{"dark_to_observed":1,"observed_to_dark":0,
                    "observed_to_observed":0,"ablate_readout":1},
 "irrelevant":{"dark_to_observed":0,"observed_to_dark":0,
               "observed_to_observed":0,"ablate_readout":0},
}


def all_min_separating_arm_sets(signatures):
    """Every minimum-cardinality nonadaptive separating set."""
    names=list(signatures)
    arms=list(next(iter(signatures.values())))
    for k in range(len(arms)+1):
        covers=[ids for ids in combinations(arms,k)
                if all(any(signatures[a][e]!=signatures[b][e] for e in ids)
                       for a,b in combinations(names,2))]
        if covers:
            return covers
    return []


# The originally registered freeze was mistaken for a selective A intervention.
# Physical freezing cancels both A and B, leaving invariant/register coincident.
CORRECTED_FREEZE_SIGNATURES={
    typ:{("freeze_U" if arm=="observed_to_observed" else arm):
         (1 if typ=="output_register" and arm=="observed_to_observed" else value)
         for arm,value in row.items()}
    for typ,row in IDEAL_SIGNATURES.items()
}


def rotation5_interior_parity():
    """Exact canonical witnesses for T=1 ⊕ R90 ⊕ R90, G=e1^T.

    Orthogonal quarter-turn dynamics on R^4 have even-dimensional real
    invariant subspaces. Thus global exact-rank closure fails at k=2,4.
    """
    T=rat([[1,0,0,0,0],
           [0,0,-1,0,0],[0,1,0,0,0],
           [0,0,0,0,-1],[0,0,0,1,0]])
    G=rat([[1,0,0,0,0]])
    values={}
    for k in (2,3,4):
        U=rat([[int(i==j) for j in range(k)] for i in range(5)])
        Q=rat([[int(i==j+k) for j in range(5-k)] for i in range(5)])
        B=mul(mul(transpose(U),minus(T,eye(5))),Q)
        values[k]=fnorm2(B)
    return {"T":T,"G":G,"B2_for_canonical_witnesses":values,
            "interior_nonmonotone":values=={2:F(1),3:F(0),4:F(1)}}


def gaussian_pair_kl(mu1,mu2,variance):
    if variance<=0:
        raise ValueError("Positive measured variance required")
    return (mu1-mu2)**2/(2*variance)


def chernoff_grid(means,variances,step=F(1,20)):
    """Four-arm 0.05-grid max-min KL allocation under equal-variance Gaussian arms.

    When means/variances are measured this estimates a declared allocation.
    The IDEAL_SIGNATURES table remains synthetic and cannot evidence neural
    allocation. The finite grid is NOT a continuous Chernoff optimum.
    """
    names=list(means)
    arms=list(next(iter(means.values())))
    if len(arms)!=4 or set(arms)!=set(variances):
        raise ValueError("Exactly the four preregistered intervention arms are required")
    N=int(1/step)
    best=None
    for x in range(N+1):
        for y in range(N-x+1):
            for z in range(N-x-y+1):
                ws=(F(x,N),F(y,N),F(z,N),F(N-x-y-z,N))
                worst=min(
                    sum((ws[i]*gaussian_pair_kl(F(means[a][arm]),
                                               F(means[b][arm]),
                                               F(variances[arm]))
                         for i,arm in enumerate(arms)),F(0))
                    for a,b in combinations(names,2))
                if best is None or (worst,tuple(-v for v in ws))>(best[0],tuple(-v for v in best[1])):
                    best=(worst,ws)
    return {"arms":arms,"worst_pair_KL":best[0],
            "allocation":best[1],"step":step,
            "status":"synthetic_or_empirical_depending_on_means_source"}


def ideal_four_arm_chernoff_exact():
    """Exact optimum for the *hypothetical* five-type binary signature table.

    Unit-variance Gaussian responses with means in {0,1} have pairwise KL
    of (mean difference)^2/2. The four arm allocation is:
      dark_to_observed = 1/5; observed_to_dark = 1/5;
      observed_to_observed = 2/5; ablate_readout = 1/5.
    Its worst-pair weighted KL is 1/5.

    Proof: let arm shares x,y,z,w sum to one. The 10 pairs include
    distances z, x+y, x+w, y+w. If their minimum is t, then
      5t <= 2z+(x+y)+(x+w)+(y+w) = 2(x+y+z+w)=2.
    Hence t<=2/5, i.e. KL<=1/5. The displayed assignment attains
    all four inequalities. This is an elementary linear program, not
    a claim of novel Chernoff theory or an empirical mechanism model.
    """
    arms=list(next(iter(IDEAL_SIGNATURES.values())))
    expected={"dark_to_observed":F(1,5),
              "observed_to_dark":F(1,5),
              "observed_to_observed":F(2,5),
              "ablate_readout":F(1,5)}
    if set(arms)!=set(expected):
        raise AssertionError("Canonical ideal table's arm labels changed")
    per_pair={}
    for a,b in combinations(IDEAL_SIGNATURES,2):
        val=sum((expected[e]*gaussian_pair_kl(
            F(IDEAL_SIGNATURES[a][e]),F(IDEAL_SIGNATURES[b][e]),F(1))
                 for e in arms),F(0))
        per_pair[a+"__"+b]=val
    if min(per_pair.values())!=F(1,5):
        raise AssertionError("Exact ideal optimum construction changed")
    return {"schema":"roc01.synthetic_ideal_chernoff_exact.v1",
            "allocation":expected,
            "worst_pair_KL":min(per_pair.values()),
            "analytic_upper_bound_KL":F(1,5),
            "per_pair_KL":per_pair,
            "interpretation":"hypothetical five-row signature; not measured neural effects",
            "minimum_separating_arm_count":len(min_separating_arm_set(IDEAL_SIGNATURES)),
            "allocation_uses_all_four_arms":all(v>0 for v in expected.values())}
