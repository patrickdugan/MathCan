"""TOE-12: both metric TT polarizations and SU(2)^2 gauge tensor channels.

A six-mode *restricted* tensor subspace of the declared two-form + bare
Yang--Mills second variation: metric (+,x); gauge (+,x) for each flavor.
This is a polarization of the exact frozen 6x6 bivector susceptibility.
It omits the full 0/1-form sector, independent G fluctuations outside the
algebraic 2-form relation, and all gauge-fixed scalar/vector constraints.
"""
from fractions import Fraction as F
from .operator_principal import (
    colored_background,wave_riemann_pair,wave_field_strength,susceptibility,
    build_theta,inverse,differential,mul,trace,S,
)
from .jordan_principal import rat,rank


def modes(omega,electric):
    """Each mode = (metric symmetric 4x4 h, six-vector dF per adjoint color)."""
    x=(rat(omega),F(),F(),F(1))
    n=len(electric)
    def hmat(cross):
        h=[[F() for _ in range(4)] for j in range(4)]
        if cross:h[1][2]=h[2][1]=F(1)
        else:h[1][1]=F(1);h[2][2]=F(-1)
        return wave_riemann_pair(x,tuple(map(tuple,h)))
    zero_r=tuple(tuple(F() for j in range(6)) for i in range(6))
    zero_fs=tuple((F(),)*6 for i in range(3*n))
    out=[(hmat(False),zero_fs),(hmat(True),zero_fs)]
    for f in range(n):
        for cross in (False,True):
            df=[]
            for i in range(n):
                for adj in range(3):
                    a=[F() for j in range(4)]
                    if i==f:
                        if cross:
                            if adj==0:a[2]=1
                            elif adj==1:a[1]=1
                        else:
                            if adj==0:a[1]=1
                            elif adj==1:a[2]=-1
                    df.append(wave_field_strength(x,a))
            out.append((zero_r,tuple(df)))
    return tuple(out)


def add_modes(left,right):
    ra,fa=left;rb,fb=right
    return (tuple(tuple(a+b for a,b in zip(x,y)) for x,y in zip(ra,rb)),
            tuple(tuple(a+b for a,b in zip(x,y)) for x,y in zip(fa,fb)))


def bilinear_matrix(omega,*,electric,magnetic,A,Bcurv,alpha,beta,sigma):
    """Independent analytic polarization of the 6x6 second variation.

    Computes cross terms with the noncommuting matrix trace rather than
    subtracting evaluations of a quadratic functional. This has the same
    curvature, gauge and color conventions as operator_principal.py.
    """
    E=tuple(map(rat,electric));B=tuple(map(rat,magnetic))
    if len(E)!=len(B) or len(E)!=2:raise ValueError('two SU(2) gauge multiplets')
    Fcol=colored_background(E,B)
    basis=modes(omega,E)
    alpha,beta,sigma=map(rat,(alpha,beta,sigma))
    G=inverse(build_theta(Fcol,A,Bcurv,alpha,beta))
    linear=[]
    for r,f in basis:
        pr,pf,_=differential(Fcol,f,r,alpha,beta)
        p=tuple(tuple(x+y for x,y in zip(a,b)) for a,b in zip(pr,pf))
        linear.append(mul(G,p))
    n=len(basis)
    result=[[F() for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i,n):
            fi=basis[i][1];fj=basis[j][1]
            pff=tuple(tuple(alpha*sum((u[k]*v[l]+v[k]*u[l]
                              for u,v in zip(fi,fj)),F())*S[l]
                            for l in range(6)) for k in range(6))
            bare=-sum((sgn*a*b for u,v in zip(fi,fj)
                        for a,b,sgn in zip(u,v,S)),F())
            value=bare+sigma*(trace(mul(linear[i],linear[j]))-
                              trace(mul(G,pff)))
            result[i][j]=value
            result[j][i]=value
    return tuple(tuple(row) for row in result)


def independent_polarization_matrix(omega,**kw):
    """Slower quadratic-polarization reconstruction for regression tests."""
    E=tuple(map(rat,kw['electric']));B=tuple(map(rat,kw['magnetic']))
    Fcol=colored_background(E,B)
    basis=modes(omega,E)
    params={k:v for k,v in kw.items() if k not in ('electric','magnetic')}
    params['B']=params.pop('Bcurv')
    def q(pair):
        r,f=pair
        t=susceptibility(Fcol,f,r,**params)
        return t['rr']+2*t['rf']+t['ff']
    base=[q(x) for x in basis]
    return tuple(tuple(base[i] if i==j else (q(add_modes(basis[i],basis[j]))-base[i]-base[j])/2
                       for j in range(len(base))) for i in range(len(base)))

def default_params():
    return dict(electric=(2,F(1001,1000)),magnetic=(1,0),
                A=F(2,5),Bcurv=1,alpha=F(3,500),beta=F(1,100),sigma=F(1,100))


def _fit_polynomial(nodes,values):
    """Solve a rational Vandermonde system, ascending coefficients."""
    n=len(nodes)
    m=[[rat(nodes[i])**j for j in range(n)]+[rat(values[i])] for i in range(n)]
    for j in range(n):
        k=next((i for i in range(j,n) if m[i][j]),None)
        if k is None:raise ValueError('distinct nodes required')
        m[j],m[k]=m[k],m[j]
        f=m[j][j]
        m[j]=[z/f for z in m[j]]
        for i in range(n):
            if i!=j:
                f=m[i][j]
                m[i]=[u-f*v for u,v in zip(m[i],m[j])]
    return tuple(m[i][-1] for i in range(n))


def interpolate_tensor(**kw):
    """All 21 entries of the six-mode tensor symbol, including chiral mixing.

    Metric-metric entries are quartic in temporal frequency, metric/gauge
    entries cubic, and gauge/gauge entries quadratic. Coefficients are
    computed from independent evaluations and verified at extra samples.
    NO parity assumption is imposed: E·B can couple + and x helicities.
    """
    wset=(F(-2),F(-1),F(),F(1),F(2))
    M={w:bilinear_matrix(w,**kw) for w in wset}
    n=len(M[wset[0]])
    out={}
    for i in range(n):
        for j in range(i,n):
            deg=4 if i<2 and j<2 else 3 if i<2 or j<2 else 2
            nodes=wset[:deg+1]
            out[(i,j)]=_fit_polynomial(nodes,[M[w][i][j] for w in nodes])
    for w in (F(-3),F(3),F(5,2),F(-5,2)):
        actual=bilinear_matrix(w,**kw)
        for (i,j),coeff in out.items():
            expected=sum((c*w**k for k,c in enumerate(coeff)),F())
            if actual[i][j]!=expected:raise AssertionError(f'polynomial mismatch {w,i,j}')
    return out


def at_frequency(coeff,w):
    """Symmetric 6x6 tensor-mode matrix from stored polynomial coefficients."""
    w=rat(w);n=6
    return tuple(tuple(sum((c*w**k for k,c in enumerate(
        coeff[(i,j)] if i<=j else coeff[(j,i)])),F())
                       for j in range(n)) for i in range(n))


def _field_add(x,y):return (x[0]+y[0],x[1]+y[1])
def _field_sub(x,y):return (x[0]-y[0],x[1]-y[1])
def _field_mul(x,y,r):return (x[0]*y[0]+r*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def _field_inv(x,r):
    norm=x[0]*x[0]-r*x[1]*x[1]
    if norm==0:raise ValueError('singular element of quadratic field')
    return (x[0]/norm,-x[1]/norm)


def _field_evaluate(coeff,r):
    """Polynomial at u with u²=r, as exact (constant, coefficient-of-u)."""
    return (sum((c*r**(k//2) for k,c in enumerate(coeff) if k%2==0),F()),
            sum((c*r**(k//2) for k,c in enumerate(coeff) if k%2==1),F()))


def field_determinant(matrix,r):
    """Exact Gaussian elimination in Q[u]/(u²-r), r nonsquare positive."""
    from math import isqrt
    r=rat(r)
    if r<=0 or isqrt(r.numerator)**2==r.numerator and isqrt(r.denominator)**2==r.denominator:
        raise ValueError('positive nonsquare quadratic extension required')
    n=len(matrix)
    if n==0 or any(len(row)!=n for row in matrix):raise ValueError('square matrix required')
    M=[[tuple(map(rat,x)) for x in row] for row in matrix]
    D=(F(1),F());pivots=0
    for j in range(n):
        k=next((i for i in range(j,n) if any(M[i][j])),None)
        if k is None:return (F(),F()),pivots
        if k!=j:
            M[j],M[k]=M[k],M[j]
            D=(-D[0],-D[1])
        v=M[j][j]
        D=_field_mul(D,v,r)
        iv=_field_inv(v,r)
        for i in range(j+1,n):
            q=_field_mul(M[i][j],iv,r)
            for k in range(j+1,n):
                M[i][k]=_field_sub(M[i][k],_field_mul(q,M[j][k],r))
            M[i][j]=(F(),F())
        pivots+=1
    return D,pivots


def factored_tensor_at_root(coeff,r):
    """Cancel one delta=(w²-r) from each metric row and column.

    The top-left metric block must contain delta², mixed entries delta.
    The 6x6 determinant then equals delta^4 times this reduced determinant.
    Everything is checked exactly in Q[sqrt(r)].
    """
    r=rat(r)
    M=[]
    for i in range(6):
        row=[]
        for j in range(6):
            c=coeff[(i,j)] if i<=j else coeff[(j,i)]
            if i<2 and j<2:
                if c!=(c[4]*r*r,F(),-2*c[4]*r,F(),c[4]):
                    raise AssertionError('metric factor is not delta²')
                row.append((c[4],F()))
            elif i<2 or j<2:
                if c!=(-r*c[2],-r*c[3],c[2],c[3]):
                    raise AssertionError('mixed factor is not delta')
                row.append((c[2],c[3]))
            else:
                row.append(_field_evaluate(c,r))
        M.append(tuple(row))
    reduced_det,reduced_rank=field_determinant(M,r)
    if reduced_rank!=6 or not any(reduced_det):
        raise AssertionError('the factor delta^4 was not exact at this root')
    G=[row[2:] for row in M[2:]]
    gauge_det,gauge_rank=field_determinant(G,r)
    if gauge_rank!=4 or not any(gauge_det):
        raise AssertionError('gauge-flavor tensor block singular at root')
    # Unfactored symbol has a 2x zero metric block and zero metric-gauge rows,
    # so rank is 4 and geometric root multiplicity is 2.
    return {'reduced_determinant':reduced_det,'reduced_rank':reduced_rank,
            'gauge_determinant':gauge_det,'gauge_rank':gauge_rank,
            'root_rank':4,'root_nullity':2,'root_det_multiplicity':4}


def tensor_certificate(**kw):
    from .wave_principal import construct_symbol
    coeff=interpolate_tensor(**kw)
    r=construct_symbol(**kw).doubled_gravity_root
    p=construct_symbol(**kw)
    if (coeff[(0,0)]!=(p.rr[0],F(),p.rr[1],F(),p.rr[2]) or
        coeff[(0,2)]!=(F(),p.rf[0],F(),p.rf[1]) or
        coeff[(2,2)]!=(p.ff[0],F(),p.ff[1])):
        raise AssertionError('source TOE-11 projection mismatch')
    parity=coeff[(0,3)]
    chiral=coeff[(1,2)]
    if parity[0]==0 or chiral[0]!=-parity[0]:
        raise AssertionError('expected electric/magnetic helicity mixing absent')
    fact=factored_tensor_at_root(coeff,r)
    # Weighted highest-derivative matrix of orders (4,4,2,2,2,2),
    # with mixed order 3, has full rank: the polynomial is regular and a
    # standard 16-state time reduction exists for this tensor projection.
    from .mixed_principal import det as exact_det
    leading=tuple(tuple((coeff[(i,j)] if i<=j else coeff[(j,i)])[
        4 if i<2 and j<2 else 3 if i<2 or j<2 else 2]
        for j in range(6)) for i in range(6))
    leading_det=exact_det(leading)
    if leading_det==0:raise AssertionError('singular 16-state leading pencil')
    return {'schema':'mathcan.toe12.tensor6.v1',
            'root_r':str(r),
            'metric_plus_to_gauge_cross_at_zero':str(parity[0]),
            'metric_cross_to_gauge_plus_at_zero':str(chiral[0]),
            'parity_sensitive_cross_helicity_coupling':True,
            'determinant_divisible_by_delta_power':fact['root_det_multiplicity'],
            'root_nullity':fact['root_nullity'],
            'weighted_leading_determinant':str(leading_det),
            'reduced_determinant':tuple(map(str,fact['reduced_determinant'])),
            'gauge_block_determinant':tuple(map(str,fact['gauge_determinant'])),
            'two_jordan_chains_in_six_mode_polynomial':True,
            'full_tensor_wave_sector_complete':False,
            'Gfield_0_1_form_or_metric_constraints_complete':False}

if __name__=='__main__':
    x=tensor_certificate(**default_params())
    print({k:str(v) for k,v in x.items()})
