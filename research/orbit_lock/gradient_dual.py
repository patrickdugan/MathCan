"""OLM-18 exact rational witnesses for gradient-inactive duality and Taylor error.

No PyTorch, floating point or external algebra packages. All small matrices
are solved by rational row elimination.
"""
from fractions import Fraction as Q


def v(xs):
    return tuple(Q(x) for x in xs)


def dot(a,b):
    if len(a)!=len(b):raise ValueError("dimension mismatch")
    return sum((a[i]*b[i] for i in range(len(a))),Q(0))


def norm_sq(xs):
    return dot(xs,xs)


def transpose(A):
    if not A or not A[0] or any(len(row)!=len(A[0]) for row in A):
        raise ValueError("matrix must be nonempty rectangular")
    return tuple(tuple(Q(A[i][j]) for i in range(len(A))) for j in range(len(A[0])))


def matmul(A,B):
    BT=transpose(B)
    return tuple(tuple(dot(v(row),col) for col in BT) for row in A)


def matvec(A,x):
    return tuple(dot(v(row),x) for row in A)


def linear_solve(A,b):
    n=len(A)
    if n==0 or len(b)!=n or any(len(row)!=n for row in A):
        raise ValueError("square system required")
    mat=[[Q(x) for x in row]+[Q(b[i])] for i,row in enumerate(A)]
    for col in range(n):
        pivot=next((r for r in range(col,n) if mat[r][col]!=0),None)
        if pivot is None:raise ValueError("matrix has deficient rank")
        mat[col],mat[pivot]=mat[pivot],mat[col]
        factor=mat[col][col]
        for j in range(col,n+1):mat[col][j]/=factor
        for r in range(n):
            if r==col:continue
            coeff=mat[r][col]
            for j in range(col,n+1):mat[r][j]-=coeff*mat[col][j]
    return tuple(row[-1] for row in mat)


def inactive_dual(B,g):
    """Minimal-norm lambda satisfying B^T lambda=g."""
    B=tuple(v(row) for row in B);g=v(g)
    BT=transpose(B)
    if len(B[0])!=len(g):
        raise ValueError("gradient and physical encoder dimension mismatch")
    gram=matmul(BT,B)
    w=linear_solve(gram,g)
    lam=matvec(B,w)
    if matvec(BT,lam)!=g:
        raise ArithmeticError("dual reconstruction differs")
    return lam


def test_dual_witness():
    B=((1,0),(0,1),(1,1))
    g=v((2,3))
    lam=inactive_dual(B,g)
    u=v((2,-1))
    shift=matvec(B,u)
    return {"lambda":lam, "reconstructed_gradient":matvec(transpose(B),lam),
            "task_directional":dot(g,u),
            "inactive_dual_directional":dot(lam,shift),
            "dual_sq":norm_sq(lam),
            "inactive_shift_sq":norm_sq(shift)}


def finite_effect(m,h,k,s):
    hh=v(h);kk=v(k);ss=v(s)
    return m(tuple(hh[i]-ss[i] for i in range(len(hh))))-m(tuple(hh[i]-kk[i] for i in range(len(hh))))


def quadratic_sharpness(r=Q(3,5),M=Q(4)):
    r,M=Q(r),Q(M)
    if r<=0 or M<0:raise ValueError("nonnegative curvature, positive radius")
    m=lambda x:M*(x[0]*x[0]-x[1]*x[1])/2
    k=v((r,0));s=v((0,r));h=v((0,0))
    measured=finite_effect(m,h,k,s)
    return {"finite_difference":measured,"linear_prediction":Q(0),
            "sharp_bound":M*r*r,"kill_sham_dot":dot(k,s)}


def cubic_sharpness(r=Q(1,5),T=Q(3)):
    r,T=Q(r),Q(T)
    if r<=0 or T<0:raise ValueError("nonnegative third bound, positive radius")
    m=lambda x:T*(x[0]**3-x[1]**3)/6
    return {"finite_difference":finite_effect(m,(0,0),(r,0),(0,r)),
            "jet_prediction":Q(0),"sharp_bound":T*r**3/3}


def second_jet_obstruction():
    a=lambda x:Q(10)+x[0]
    b=lambda x:Q(10)+x[0]-3*x[0]**3
    return {"clean_margin":a((Q(0),Q(0))),
            "common_gradient":v((1,0)),
            "common_hessian":((Q(0),Q(0)),(Q(0),Q(0))),
            "finite_A":finite_effect(a,(0,0),(1,0),(0,1)),
            "finite_B":finite_effect(b,(0,0),(1,0),(0,1))}


if __name__=="__main__":
    import json
    def show(x):
        if isinstance(x,Q):return str(x)
        if isinstance(x,tuple):return list(map(show,x))
        raise TypeError(type(x))
    print(json.dumps({"inactive_dual":test_dual_witness(),
                      "quadratic":quadratic_sharpness(),
                      "cubic":cubic_sharpness(),
                      "second_jet_obstruction":second_jet_obstruction()},
                     default=show,indent=2))
