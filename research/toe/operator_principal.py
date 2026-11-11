"""TOE-11: principal *susceptibility* of the specified non-Abelian 2-form trial.

In a local orthonormal frame with bivector metric S=(-I3,+I3), define
 Theta = I + alpha*G*S - beta*Rpair, with G=sum_F F F^T.
For frozen (g,F,R) backgrounds, the exact bilinear second variation of
 L = -1/4 sum F_ab F^ab - sigma log(det(Theta)) is
  K_RR = sigma tr(T^-1 P_R T^-1 P_R)
  K_RF = sigma tr(T^-1 P_R T^-1 P_F)
  K_FF = YM -sigma tr(T^-1 P_FF) + sigma tr(T^-1 P_F T^-1 P_F).

P_R is a curvature-pair-operator perturbation and P_F is a first variation
of the color-invariant field-strength Gram operator. The Riemann tensor and
field strength symbols carry 2 and 1 powers of wave covector respectively.
Thus the mixed term has 3 derivatives in a local Fourier/WKB calculation.

This is the 2-form contribution of a *declared* action. The complete GfE
operator includes scalar/one-form/G fields. A physical characteristic matrix
also needs the Riemann algebraic symmetries, metric and gauge constraints,
and suitable gauge-fixing/symmetrizer. Nothing here certifies hyperbolicity.
"""
from __future__ import annotations
from fractions import Fraction as Q
from .mixed_principal import rat

PAIR=((0,1),(0,2),(0,3),(2,3),(3,1),(1,2))
S=(-1,-1,-1,1,1,1)
N=6


def identity():return tuple(tuple(Q(i==j) for j in range(N)) for i in range(N))
def zeros():return tuple(tuple(Q() for j in range(N)) for i in range(N))

def mul(A,B):
    return tuple(tuple(sum((A[i][k]*B[k][j] for k in range(len(B))),Q())
                       for j in range(len(B[0]))) for i in range(len(A)))

def trace(A):return sum((A[i][i] for i in range(len(A))),Q())

def inverse(A):
    if len(A)!=N or any(len(row)!=N for row in A):
        raise ValueError('6x6 bivector matrix required')
    M=[[rat(a) for a in row]+[Q(i==j) for j in range(N)] for i,row in enumerate(A)]
    for j in range(N):
        pivot=next((i for i in range(j,N) if M[i][j]!=0),None)
        if pivot is None:raise ValueError('singular induced bivector operator')
        M[j],M[pivot]=M[pivot],M[j]
        p=M[j][j]
        M[j]=[x/p for x in M[j]]
        for i in range(N):
            if i==j:continue
            p=M[i][j]
            if p:M[i]=[x-p*y for x,y in zip(M[i],M[j])]
    return tuple(tuple(x for x in row[N:]) for row in M)


def colored_background(electric,magnetic):
    """One 6-vector per SU(2) adjoint color and gauge flavor."""
    E=tuple(map(rat,electric));B=tuple(map(rat,magnetic))
    if len(E)!=len(B) or not E:raise ValueError('nonempty same-length flavors')
    return tuple(tuple((E[i] if k==a else B[i] if k==a+3 else Q())
                       for k in range(N)) for i in range(len(E)) for a in range(3))


def electric_flavor_change(nflavor,index,value=1):
    """Infinitesimal change of one flavor's physical E_i at fixed B_i."""
    if not 0<=index<nflavor:raise ValueError('flavor index')
    v=rat(value)
    return tuple(tuple(v if i==index and k==a else Q() for k in range(N))
                 for i in range(nflavor) for a in range(3))


def gram(F):
    if not F or any(len(x)!=N for x in F):raise ValueError('bivector field shapes')
    return tuple(tuple(sum((f[i]*f[j] for f in F),Q()) for j in range(N)) for i in range(N))


def gram_first(F,dF):
    if len(F)!=len(dF) or any(len(f)!=N for f in dF):raise ValueError('field perturbation shapes')
    return tuple(tuple(sum((f[i]*d[j]+d[i]*f[j] for f,d in zip(F,dF)),Q())
                       for j in range(N)) for i in range(N))


def gram_second(dF):
    return tuple(tuple(2*sum((d[i]*d[j] for d in dF),Q())
                       for j in range(N)) for i in range(N))


def pair_curvature(A,B):
    A,B=rat(A),rat(B)
    return tuple(tuple((2*A if i<3 else 2*B) if i==j else Q()
                       for j in range(N)) for i in range(N))


def pair_curvature_first(dA,dB=0):return pair_curvature(dA,dB)


def build_theta(F,A,B,alpha,beta):
    alpha,beta=rat(alpha),rat(beta)
    if alpha<=0 or beta<=0:raise ValueError('positive alpha/beta required')
    G=gram(F);R=pair_curvature(A,B)
    T=tuple(tuple(Q(i==j)+alpha*G[i][j]*S[j]-beta*R[i][j]
                  for j in range(N)) for i in range(N))
    return T


def differential(F,dF,dR,alpha,beta):
    alpha,beta=rat(alpha),rat(beta)
    if len(dR)!=N or any(len(row)!=N for row in dR):raise ValueError('curvature pair shape')
    PR=tuple(tuple(-beta*rat(dR[i][j]) for j in range(N)) for i in range(N))
    PF=tuple(tuple(alpha*gram_first(F,dF)[i][j]*S[j] for j in range(N)) for i in range(N))
    PFF=tuple(tuple(alpha*gram_second(dF)[i][j]*S[j] for j in range(N)) for i in range(N))
    return PR,PF,PFF


def susceptibility(F, dF, dR, *, A,B,alpha,beta,sigma):
    """Exact second-variation principal coefficients for one perturbation pair."""
    sigma=rat(sigma)
    if sigma<0:raise ValueError('sigma>=0')
    T=build_theta(F,A,B,alpha,beta)
    J=inverse(T)
    PR,PF,PFF=differential(F,dF,dR,alpha,beta)
    jr,jf=(mul(J,P) for P in (PR,PF))
    rr=sigma*trace(mul(jr,jr))
    rf=sigma*trace(mul(jr,jf))
    bare=-sum((sgn*f*f for d in dF for sgn,f in zip(S,d)),Q())
    ff=bare+sigma*(trace(mul(jf,jf))-trace(mul(J,PFF)))
    return {'rr':rr,'rf':rf,'ff':ff,'ym':bare,'theta':T}


def wave_riemann_pair(xi,h):
    """Coordinate-principal linear Riemann delta R_{ab cd} in flat local frame.

    R_abcd = [xi_c xi_b h_ad + xi_d xi_a h_bc
              -xi_d xi_b h_ac -xi_c xi_a h_bd]/2.
    R_pair[I,J]=2*R_abcd*S[J], consistent with the 2A/2B FLRW convention.
    The wave-vector symbol uses derivatives -> xi; the Fourier i factors
    are external and must be restored for actual dispersion calculations.
    """
    if len(xi)!=4 or len(h)!=4 or any(len(row)!=4 for row in h):
        raise ValueError('four-dimensional wave/metric perturbation required')
    xi=tuple(map(rat,xi));h=tuple(tuple(map(rat,row)) for row in h)
    if any(h[i][j]!=h[j][i] for i in range(4) for j in range(4)):
        raise ValueError('metric perturbation must be symmetric')
    def r(a,b,c,d):
        return (xi[c]*xi[b]*h[a][d]+xi[d]*xi[a]*h[b][c]
               -xi[d]*xi[b]*h[a][c]-xi[c]*xi[a]*h[b][d])/2
    M=tuple(tuple(2*r(a,b,c,d)*S[j] for j,(c,d) in enumerate(PAIR))
            for a,b in PAIR)
    # Pair-exchange symmetry for Rcov, and algebraic first Bianchi.
    for i in range(N):
        for j in range(N):
            assert M[i][j]*S[j]==M[j][i]*S[i]
    assert r(0,1,2,3)+r(0,2,3,1)+r(0,3,1,2)==0
    return M


def wave_field_strength(xi,a):
    """Bivector field strength of one color-amplitude one-form a_mu."""
    if len(xi)!=4 or len(a)!=4:raise ValueError('four-dimensional covector required')
    x=tuple(map(rat,xi));v=tuple(map(rat,a))
    return tuple(x[i]*v[j]-x[j]*v[i] for i,j in PAIR)


def all_zero_curvature():return zeros()


def wave_example():
    """One kinematic Fourier direction, for a metric/gauge spin-2 amplitude.

    This reports 2-form principal susceptibility only. It does not compute
    the coupled symbol including all GfE form sectors or gauge constraints.
    """
    F=colored_background((2,Q(1001,1000)),(1,0))
    h=tuple(tuple(Q(1 if i==j==1 else -1 if i==j==2 else 0)
                  for j in range(4)) for i in range(4))
    xi=(1,0,0,1)
    # Perturb one gauge flavor's color-space symmetric-traceless component.
    dF=[]
    for flav in range(2):
        for adj in range(3):
            vec=(0,Q(1 if adj==0 and flav==0 else -1 if adj==1 and flav==0 else 0),0,0)
            # color 1 gets a_x, color 2 gets a_y: verify structure below.
            if flav==0 and adj==1:vec=(0,0,-1,0)
            dF.append(wave_field_strength(xi,vec))
    x=susceptibility(F,dF,wave_riemann_pair(xi,h),
                     A=Q(2,5),B=1,alpha=Q(3,500),beta=Q(1,100),sigma=Q(1,100))
    return {'gravitational_highest':str(x['rr']),
            'mixed_third_derivative':str(x['rf']),
            'gauge_second_derivative':str(x['ff']),
            'only_declared_two_form_sector':True}

if __name__=='__main__':
    print(wave_example())
