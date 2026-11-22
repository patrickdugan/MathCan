"""DEL-07 exact rational model of Katz restriction and Poincare-dual Gysin.

For a restriction R: H_X -> H_Y, and perfect pairings
    P_X : C_X -> H_X*,  P_Y : C_Y -> H_Y*,
the transpose Gysin map is
    G = inv(P_X) * transpose(R) * P_Y.

The ordinary maps below are INVERSE geometric Frobenius actions:
    A_Y R = R A_X.
The dual compact Frobenius matrices become
    B_X = inv(P_X) A_X^T P_X,
    B_Y = inv(P_Y) A_Y^T P_Y,
and satisfy G B_Y = B_X G.

This is exact matrix linear algebra. Actual etale cohomology, PD and Katz
weak Lefschetz are external geometric premises.
"""
from fractions import Fraction as F
from research.deligne_sign_audit.geometry_trace import mat, shape, multiply, inverse, eye, power, trace


def transpose(A):
    n,m=shape(A)
    return tuple(tuple(A[i][j] for i in range(n)) for j in range(m))


def rank(A):
    n,m=shape(A)
    w=[list(map(F,row)) for row in A]
    pivots=[]
    i=0
    for j in range(m):
        p=next((h for h in range(i,n) if w[h][j]!=0),None)
        if p is None: continue
        w[i],w[p]=w[p],w[i]
        t=w[i][j]
        w[i]=[x/t for x in w[i]]
        for h in range(n):
            if h==i: continue
            t=w[h][j]
            w[h]=[u-t*v for u,v in zip(w[h],w[i])]
        pivots.append(j)
        i+=1
        if i==n: break
    return len(pivots)


def add(A,B):
    n,m=shape(A)
    if shape(B)!=(n,m):raise ValueError("shape mismatch")
    return tuple(tuple(A[i][j]+B[i][j] for j in range(m)) for i in range(n))


def gysin(R,PX,PY):
    ry,rx=shape(R)
    if shape(PX)!=(rx,rx) or shape(PY)!=(ry,ry):
        raise ValueError("PD perfect pairing shape mismatch")
    return multiply(multiply(inverse(PX),transpose(R)),PY)


def compact_frob(Ainv,P):
    """The contragredient of inverse ORDINARY Frobenius through PD."""
    return multiply(multiply(inverse(P),transpose(Ainv)),P)



def compact_frob_tate(Ainv,P,scalar):
    """Poincare dual inverse Frobenius with its required Tate scalar."""
    B=compact_frob(Ainv,P)
    t=F(scalar)
    return tuple(tuple(t*v for v in row) for row in B)


def tate_equivariance_certificate(R,PX,PY,AXinv,AYinv,tX,tY):
    """Compare G B_Y = B_X G with possibly mismatched Tate scalars."""
    G=gysin(R,PX,PY)
    BX=compact_frob_tate(AXinv,PX,tX)
    BY=compact_frob_tate(AYinv,PY,tY)
    return multiply(G,BY)==multiply(BX,G)


def compose_certificate(R,PX,PY,AXinv,AYinv,n=3):
    ry,rx=shape(R)
    if shape(AXinv)!=(rx,rx) or shape(AYinv)!=(ry,ry):
        raise ValueError("Frobenius shape mismatch")
    G=gysin(R,PX,PY)
    BX=compact_frob(AXinv,PX)
    BY=compact_frob(AYinv,PY)
    res_left=multiply(AYinv,R)
    res_right=multiply(R,AXinv)
    eq_left=multiply(G,BY)
    eq_right=multiply(BX,G)
    return {
      "restriction_injective":rank(R)==rx,
      "gysin_surjective":rank(G)==rx,
      "restriction_equivariant":res_left==res_right,
      "gysin_equivariant":eq_left==eq_right,
      "pdX_invertible":True,"pdY_invertible":True,
      "trace_difference":trace(power(BY,n))-trace(power(BX,n)),
      "gysin":G,"compact_X":BX,"compact_Y":BY,
    }


def example(a=2,b=3,c=5,u=7,v=-2,p=1,s=2,t=-1):
    """Katz injective boundary: 2-dim ordinary X -> 3-dim ordinary Y."""
    R=mat([[1,0],[0,1],[0,0]])
    AX=mat([[a,1],[0,b]])
    AY=mat([[a,1,u],[0,b,v],[0,0,c]])
    PX=mat([[1,p],[0,1]])
    PY=mat([[1,0,0],[s,1,0],[0,t,1]])
    return R,PX,PY,AX,AY


def kernel_generator(PY):
    """For R=[I_2;0], a generator of ker(inv(PX) R^T PY)."""
    z=mat([[0],[0],[1]])
    return multiply(inverse(PY),z)


def kernel_action_certificate(R,PX,PY,AX,AY,n=3):
    certificate=compose_certificate(R,PX,PY,AX,AY,n=n)
    G=certificate["gysin"]
    BY=certificate["compact_Y"]
    z=kernel_generator(PY)
    Gz=multiply(G,z)
    Gfz=multiply(G,multiply(BY,z))
    kern_eig=trace(AY)-trace(AX)
    z_eig=tuple(tuple(kern_eig*col for col in row) for row in z)
    return {
        "gysin_annihilates_generator":Gz==mat([[0],[0]]),
        "frob_preserves_kernel":Gfz==mat([[0],[0]]),
        "kernel_eigenvalue":kern_eig,
        "generator_is_eigenvector":multiply(BY,z)==z_eig,
        "trace_difference_matches":certificate["trace_difference"]==kern_eig**n,
        **certificate,
    }


def wrong_forward_dual_certificate(R,PX,PY,AX,AY):
    G=gysin(R,PX,PY)
    BY=multiply(multiply(inverse(PY),AY),PY)
    BX=multiply(multiply(inverse(PX),AX),PX)
    return multiply(G,BY)==multiply(BX,G)
