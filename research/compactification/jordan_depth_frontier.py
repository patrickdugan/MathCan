"""NRF-07: exact-rational Jordan depth and observation crossover algebra."""
from __future__ import annotations
from fractions import Fraction as Q

def product(A, B):
    if len(A) != 2 or len(B) != 2 or any(len(row) != 2 for row in (*A, *B)):
        raise ValueError("two by two matrices required")
    return tuple(tuple(sum((A[i][k] * B[k][j] for k in range(2)), Q(0))
                       for j in range(2)) for i in range(2))

def jordan_matrix(a, b):
    return ((Q(a), Q(b)), (Q(0), Q(a)))

def jordan_power(a, b, n):
    """Closed form (aI+bN)^n; N^2=0. Covers a=0 and n=0."""
    if n < 0:
        raise ValueError("nonnegative depth required")
    a, b = Q(a), Q(b)
    if n == 0:
        return jordan_matrix(1, 0)
    return jordan_matrix(a**n, n * a**(n-1) * b)

def repeated_product(a, b, n):
    if n < 0:
        raise ValueError("nonnegative depth required")
    out = jordan_matrix(1, 0)
    for _ in range(n):
        out = product(out, jordan_matrix(a, b))
    return out

def rational_circle(t):
    """Dense rational subset of the unit circle."""
    t = Q(t)
    return ((1-t*t)/(1+t*t), (2*t)/(1+t*t))

def rank_one_error_and_leakage(a,b,n,u):
    """Task e1, isotropic input; ||P J^n (I-P)||_F where P=uu^T."""
    if n < 1:
        raise ValueError("positive depth required")
    u1,u2=map(Q,u)
    if u1*u1+u2*u2 != 1:
        raise ValueError("unit observation vector required")
    E=u2*u2
    c=n*abs(Q(a))**(n-1)*abs(Q(b))
    return E,c*(1-E)

def direct_leakage_sq(a,b,n,u):
    u1,u2=map(Q,u)
    P=((u1*u1,u1*u2),(u1*u2,u2*u2))
    I=((1-P[0][0],-P[0][1]),(-P[1][0],1-P[1][1]))
    J=jordan_power(a,b,n)
    M=product(product(P,J),I)
    return sum((x*x for row in M for x in row),Q(0))

def crossover_lambda(a,b,n,better_error,worse_error):
    """λ*: (E_A+λL_A²)=(E_B+λL_B²) for E_A<E_B."""
    e1,e2=Q(better_error),Q(worse_error)
    if not (0 <= e1 < e2 <= 1) or n < 1:
        raise ValueError("ordered distinct risk values and positive depth needed")
    c=n*abs(Q(a))**(n-1)*abs(Q(b))
    if c == 0:
        return None
    return 1/(c*c*(2-e1-e2))

def objective(a,b,n,error,lam):
    if not 0 <= Q(error) <= 1 or Q(lam) < 0:
        raise ValueError("risk or penalty outside domain")
    c=n*abs(Q(a))**(n-1)*abs(Q(b))
    return Q(error)+Q(lam)*c*c*(1-Q(error))**2

def optimum_risk(a,b,n,lam):
    if Q(lam) < 0 or n < 1:
        raise ValueError("invalid regularization")
    c=n*abs(Q(a))**(n-1)*abs(Q(b))
    strength=2*Q(lam)*c*c
    return Q(0) if strength <= 1 else 1-1/strength
