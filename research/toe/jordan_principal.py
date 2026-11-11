"""TOE-12: exact-rational Jordan and gauge-null audit of TOE-11's trial symbol.

All six-dimensional companion statements apply to the FROZEN restricted
1-metric/1-Yang-Mills tensor wave polynomial from TOE-11. They do not claim
that the six-dimensional matrix is the gauge-fixed full Lambda-GfE system.

The first-order companion uses a formal real frequency indeterminate t:
 P_hh = r4*t^4+r2*t^2+r0,
 P_hg = m3*t^3+m1*t,  P_gg = f2*t^2+f0.
The off-diagonal is a formal polynomial coefficient; a physical Fourier
operator must place i phases consistently with its adjoint. The Jordan and
polynomial multiplicity claims are invariant under the corresponding
invertible constant polarization rephasing where applicable.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F

from .wave_principal import RestrictedSymbol,construct_symbol,evaluate_polynomial


def rat(x):
    if isinstance(x,bool):
        raise ValueError('boolean input')
    return F(x)


def eye(n):
    return tuple(tuple(F(int(i==j)) for j in range(n)) for i in range(n))


def zero(n,m=None):
    return tuple(tuple(F() for _ in range(n if m is None else m)) for _ in range(n))


def mm(A,B):
    if not A or not B or len(A[0])!=len(B) or any(len(x)!=len(A[0]) for x in A) or any(len(y)!=len(B[0]) for y in B):
        raise ValueError('matrix shape mismatch')
    return tuple(tuple(sum((A[i][k]*B[k][j] for k in range(len(B))),F())
                       for j in range(len(B[0]))) for i in range(len(A)))


def add(A,B,ka=1,kb=1):
    if len(A)!=len(B) or any(len(x)!=len(y) for x,y in zip(A,B)):
        raise ValueError('matrix shape mismatch')
    ka,kb=rat(ka),rat(kb)
    return tuple(tuple(ka*a+kb*b for a,b in zip(x,y)) for x,y in zip(A,B))


def diag_shift(A,amount):
    return add(A,eye(len(A)),1,amount)


def rank(A):
    if not A:return 0
    M=[list(map(rat,row)) for row in A]
    n=len(M);m=len(M[0])
    if any(len(row)!=m for row in M):raise ValueError('jagged matrix')
    r=0
    for col in range(m):
        k=next((j for j in range(r,n) if M[j][col]),None)
        if k is None:continue
        M[r],M[k]=M[k],M[r]
        p=M[r][col]
        for j in range(r+1,n):
            ratio=M[j][col]/p
            for l in range(col+1,m):M[j][l]-=ratio*M[r][l]
            M[j][col]=F()
        r+=1
        if r==n:break
    return r


def charpoly(A):
    """Independent Faddeev-LeVerrier characteristic polynomial, descending."""
    n=len(A)
    if n==0 or any(len(row)!=n for row in A):raise ValueError('square required')
    B=eye(n); coefficients=[F(1)]
    for k in range(1,n+1):
        D=mm(A,B)
        ck=-sum((D[i][i] for i in range(n)),F())/k
        coefficients.append(ck)
        B=diag_shift(D,ck)
    return tuple(coefficients)


@dataclass(frozen=True)
class Polynomial:
    """Formal Euler polynomial with orders 4,3,2, for momentum p=1."""
    r4:F;r2:F;r0:F;m3:F;m1:F;f2:F;f0:F

    def determinant(self):
        """Ascending in x=t^2, det(P_hh P_gg - P_hg^2)."""
        a,b,c,d,e,f,g=(self.r4,self.r2,self.r0,self.m3,self.m1,self.f2,self.f0)
        return (c*g, b*g+c*f-e*e, a*g+b*f-2*d*e, a*f-d*d)

    def companion(self):
        """6-state first-order formal ODE [h,h',h'',h''',g,g'].

        Eliminate g'' using the 2nd equation and differentiate once to
        eliminate g''' jointly with h''''. Requires nonzero f2 and leading
        mixed-weight determinant r4*f2-m3^2.
        """
        a,b,c,d,e,f,g=(self.r4,self.r2,self.r0,self.m3,self.m1,self.f2,self.f0)
        den=a*f-d*d
        if not f or not den:raise ValueError('nonregular high-derivative system')
        M=[[F() for _ in range(6)] for _ in range(6)]
        for i,j in ((0,1),(1,2),(2,3),(4,5)):M[i][j]=F(1)
        M[3][0]=-f*c/den
        M[3][2]=(-f*b+d*e)/den
        M[3][5]=(-f*e+d*g)/den
        M[5][1]=-e/f
        M[5][3]=-d/f
        M[5][4]=-g/f
        return tuple(tuple(row) for row in M)

    def expected_companion_polynomial(self):
        h=self.determinant();lead=h[3]
        if not lead:raise ValueError('singular leading pencil')
        return (F(1),F(),h[2]/lead,F(),h[1]/lead,F(),h[0]/lead)

    def at(self,w):
        w=rat(w);x=w*w
        return ((self.r4*x*x+self.r2*x+self.r0,w*(self.m3*x+self.m1)),
                (w*(self.m3*x+self.m1),self.f2*x+self.f0))


def polynomial(sym:RestrictedSymbol):
    return Polynomial(sym.rr[2],sym.rr[1],sym.rr[0],sym.rf[1],sym.rf[0],sym.ff[1],sym.ff[0])


def exact_example():
    return construct_symbol(electric=(2,F(1001,1000)),magnetic=(1,0),
                            A=F(2,5),Bcurv=1,alpha=F(3,500),
                            beta=F(1,100),sigma=F(1,100))


def jordan_certificate(sym:RestrictedSymbol|None=None):
    """Exact rank-2 nonzero square-zero polynomial in the 6x6 companion."""
    sym=exact_example() if sym is None else sym
    p=polynomial(sym)
    c=p.companion();cp=charpoly(c)
    r=sym.doubled_gravity_root;s=sym.remaining_root()
    if r<=0 or s is None or s<=0 or r==s:raise ValueError('two distinct positive characteristic speeds required')
    expected=(F(1),F(),-2*r-s,F(),r*r+2*r*s,F(),-r*r*s)
    if cp!=expected or cp!=p.expected_companion_polynomial():raise AssertionError('independent characteristic mismatch')
    a,b=diag_shift(mm(c,c),-r),diag_shift(mm(c,c),-s)
    N=mm(a,b)
    if N==zero(6) or mm(N,N)!=zero(6) or rank(N)!=2:raise AssertionError('Jordan witness invalid')
    assert p.r4*r*r+p.r2*r+p.r0==0
    assert p.m3*r+p.m1==0
    assert p.f2*r+p.f0!=0
    assert rank(((F(),F()),(F(),p.f2*r+p.f0)))==1
    return {'schema':'mathcan.toe12.jordan.v1',
        'scope':'restricted formal TOE-11 tensor polarization, not complete GfE gauge-fixed PDE',
        'root_r':str(r),'root_s':str(s),
        'characteristic':list(map(str,cp)),
        'nonzero_nilpotent_rank':rank(N),'nilpotent_square_zero':True,
        'eigenmatrix_rank_at_r':1,'repeated_root_geometric_multiplicity':1,
        'positive_uniform_symmetrizer_for_this_companion':False,
        'full_theory_hyperbolicity_verified':False}


def determinant_completion(sym:RestrictedSymbol|None=None, epsilon_scale=10000):
    """Toy omitted-sector correction epsilon*p²*(omega²-r p²) to P_hh.

    A source completion can alter the multiplicity of a restricted root.
    This term is a deliberately hypothetical homogeneous quartic addition,
    not an identified Lambda-GfE missing-sector contribution.
    """
    sym=exact_example() if sym is None else sym
    p=polynomial(sym)
    if type(epsilon_scale) is not int or epsilon_scale<=0:raise ValueError('positive integer scale')
    r=sym.doubled_gravity_root;s=sym.remaining_root()
    eps=p.r4/epsilon_scale
    corrected=Polynomial(p.r4,p.r2+eps,p.r0-eps*r,p.m3,p.m1,p.f2,p.f0)
    C=corrected.companion()
    if charpoly(C)!=corrected.expected_companion_polynomial():raise AssertionError('completion companion')
    def gauge_factor(x):return p.f2*x+p.f0
    def Q(x):return eps*gauge_factor(x)+(x-r)*(p.r4*gauge_factor(x)-p.m3*p.m3*x)
    left=r-F(1,1000)
    if not (0<left<r<s and Q(left)>0 and Q(r)<0 and Q(s)>0):
        raise AssertionError('required exact positive-root isolating intervals failed')
    # det = (x-r)Q(x), and quadratic Q has exactly one root per interval.
    for x in (left,r,s):
        assert evaluate_polynomial(corrected.determinant(),x)==(x-r)*Q(x)
    return {'epsilon':str(eps),'old_root':str(r),'old_third_root':str(s),
            'left_interval':(str(left),str(r)),'right_interval':(str(r),str(s)),
            'Q_at_brackets':(str(Q(left)),str(Q(r)),str(Q(s))),
            'three_distinct_positive_x_roots':True,
            'full_physics_completion':False}


PAIRS=((0,1),(0,2),(0,3),(1,2),(1,3),(2,3))
METRIC=(-1,1,1,1)


def wedge_matrix(xi):
    """Linear map on 4-vector amplitudes a -> xi wedge a, in 6 pair order."""
    if len(xi)!=4:raise ValueError('4-dimensional wave covector required')
    xi=tuple(map(rat,xi))
    return tuple(tuple(xi[i]*(k==j)-xi[j]*(k==i) for k in range(4))
                 for i,j in PAIRS)


def wedge(xi,a):
    if len(a)!=4:raise ValueError('4-dimensional gauge amplitude required')
    a=tuple(map(rat,a));return tuple(sum((x*y for x,y in zip(row,a)),F()) for row in wedge_matrix(xi))


def gauge_slice(xi,a):
    """Exact quotient by a -> a+t xi, selecting first nonzero pivot."""
    xi=tuple(map(rat,xi));a=tuple(map(rat,a))
    if len(xi)!=4 or len(a)!=4 or not any(xi):raise ValueError('nonzero 4-wave covector and amplitude required')
    pivot=next(i for i,v in enumerate(xi) if v)
    multiplier=a[pivot]/xi[pivot]
    rep=tuple(a[i]-multiplier*xi[i] for i in range(4))
    assert rep[pivot]==0 and wedge(xi,a)==wedge(xi,rep)
    assert rank(wedge_matrix(xi))==3
    return {'pivot':pivot,'removed_gauge':multiplier,'representative':rep,
            'field_strength':wedge(xi,a),'quotient_rank':3}


def lorenz_gauss(xi,a):
    """Bare YM principal Gauss operator: xi² a_nu-xi_nu*(xi raised dot a).

    Background gauge commutators are lower-derivative. Nonminimal TOE-10
    response can change this principal equation and is NOT included here.
    """
    xi=tuple(map(rat,xi));a=tuple(map(rat,a))
    if len(xi)!=4 or len(a)!=4:raise ValueError('four-vector input')
    norm=sum((METRIC[i]*xi[i]*xi[i] for i in range(4)),F())
    pair=sum((METRIC[i]*xi[i]*a[i] for i in range(4)),F())
    return tuple(norm*a[i]-xi[i]*pair for i in range(4))


def bare_null_cone_physical_basis():
    xi=(F(1),F(),F(),F(1))
    transverse=((F(),F(1),F(),F()),(F(),F(),F(1),F()))
    assert rank(wedge_matrix(xi))==3
    assert all(lorenz_gauss(xi,a)==(F(),)*4 for a in transverse)
    assert gauge_slice(xi,xi)['representative']==(F(),)*4
    # For the fixed gauge a0=0, Gauss enforces a3=0 (two transverse amplitudes).
    return {'covector':tuple(map(str,xi)),'pure_gauge_nullity_per_color':1,
            'quotient_dimension_per_color':3,'on_shell_transverse_modes_per_color':2,
            'six_SU2_adjoint_colors':6,'bare_total_transverse_modes':12,
            'nonminimal_gauge_constraints_derived':False}


def reference_experiment():
    return {'jordan':jordan_certificate(),
            'hypothetical_completion':determinant_completion(),
            'bare_yang_mills_gauge':bare_null_cone_physical_basis()}

if __name__=='__main__':
    import json
    print(json.dumps(reference_experiment(),indent=2,sort_keys=True))
