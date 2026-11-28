"""NRF-10: exact rational Gram identity and projector-motion leakage bound.

The perturbation inequality uses the Frobenius norm to upper-bound the
operator norm. This is a conservative but exact rational certificate.
"""
from fractions import Fraction as Q


def mat(rows):
    if not rows or any(len(r)!=len(rows) for r in rows):
        raise ValueError('nonempty square matrix required')
    return tuple(tuple(Q(x) for x in r) for r in rows)


def identity(n):
    if n<1:raise ValueError('positive dimension required')
    return mat([[int(i==j) for j in range(n)] for i in range(n)])


def mul(A,B):
    n=len(A)
    if n!=len(B) or any(len(r)!=n for r in (*A,*B)):
        raise ValueError('same-dimension square matrices required')
    return tuple(tuple(sum((A[i][k]*B[k][j] for k in range(n)),Q(0))
                       for j in range(n)) for i in range(n))


def add(A,B):
    return tuple(tuple(x+y for x,y in zip(a,b)) for a,b in zip(A,B))


def sub(A,B):
    return tuple(tuple(x-y for x,y in zip(a,b)) for a,b in zip(A,B))


def frob2(A):
    return sum((x*x for row in A for x in row),Q(0))


def projector_from_circle(t):
    t=Q(t)
    u=((1-t*t)/(1+t*t),2*t/(1+t*t))
    return mat([[u[i]*u[j] for j in range(2)] for i in range(2)])


def complement(P):
    return sub(identity(len(P)),P)


def check_projector(P):
    if P!=tuple(zip(*P)) or mul(P,P)!=P:
        raise ValueError('orthogonal projector required')


def gram_dark_squared(P,J):
    """||PJQ||_F² = ||PJ||_F² - ||PJP||_F², exactly."""
    check_projector(P)
    Qp=complement(P)
    left=frob2(mul(mul(P,J),Qp))
    right=frob2(mul(P,J))-frob2(mul(mul(P,J),P))
    if left!=right:raise AssertionError('projector Gram identity failed')
    return left


def gram_shear_squared(b,t):
    """J=I+bE12; for 2D rank-one P, observed-dark leakage²=b²*u1⁴."""
    J=mat([[1,Q(b)],[0,1]])
    P=projector_from_circle(t)
    u1=(1-Q(t)*Q(t))/(1+Q(t)*Q(t))
    actual=gram_dark_squared(P,J)
    expected=Q(b)**2*u1**4
    if actual!=expected:raise AssertionError('Jordan rank-one formula failed')
    return actual


def full_motion_bound_squared(P,R,J):
    """||RJ(I-R)-PJ(I-P)||_F² <=4||J||_F²||R-P||_F²."""
    check_projector(P);check_projector(R)
    if len(J)!=len(P):raise ValueError('Jacobian dimensions differ')
    from_P=mul(mul(P,J),complement(P))
    from_R=mul(mul(R,J),complement(R))
    change=frob2(sub(from_R,from_P))
    bound=4*frob2(J)*frob2(sub(R,P))
    if change>bound:raise AssertionError('Frobenius motion bound broken')
    return change,bound


def jensen_gap(per_state_leakages):
    """Exact E[L²]-(E[L])², nonnegative for any rational scores."""
    xs=[Q(v) for v in per_state_leakages]
    if not xs or min(xs)<0:raise ValueError('nonnegative nonempty leakage needed')
    n=len(xs)
    return sum((x*x for x in xs),Q(0))/n - (sum(xs,Q(0))/n)**2
