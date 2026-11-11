"""TOE-08: exact flat-FLRW antisymmetric 2-form triad, source response and EOM.

These are MathCan-defined field equations, not a derived Dirac--Kahler
multi-multiplet solution of Gravity from Entropy. We use an O(3) internal triad,
mostly-plus signature, and independent 2-form potential B^a with H^a=dB^a.

Action per species:
 L = -H_{mu nu rho} H^{mu nu rho}/12 - m2 B_{mu nu}B^{mu nu}/4
     + lambda R_{mu nu rho sigma}B^{mu nu}B^{rho sigma}/4.
The Riemann term has an explicit source tensor but its FLRW reduction alone
cannot establish GfE's complete four-dimensional dressed stress tensor.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from typing import Sequence


def q(v):
    if type(v) is bool:
        raise ValueError('booleans are not valid field parameters')
    return F(v)


def _safe_params(m2, lam):
    m2, lam = q(m2), q(lam)
    if m2 < 0:
        raise ValueError('negative mass squared is excluded in this branch')
    return m2, lam


@dataclass(frozen=True)
class TriadStress:
    rho: F
    pressure: F
    bare_rho: F
    bare_pressure: F
    curvature_rho: F
    curvature_pressure: F


def stress(H, hdot, b, v, m2=0, lam=0) -> TriadStress:
    """FLRW matter T^0_0=-rho and T^i_j=p delta^i_j via lapse/a variations.

    v = dot(b) + 2 H b is the physical electric 3-form amplitude.  Three
    spatial 2-form orientations are summed.  This is the total matter-source
    background stress for the declared action, including the nonminimal term.
    """
    H, hdot, b, v = map(q, (H, hdot, b, v))
    m2, lam = _safe_params(m2, lam)
    bare_rho = F(3,2)*(v*v + m2*b*b)
    bare_p = F(1,2)*(-v*v + m2*b*b)
    nonmin_rho = 3*lam*H*H*b*b
    nonmin_p = 3*lam*H*H*b*b - 2*lam*(hdot+H*H)*b*b - 4*lam*H*b*v
    return TriadStress(bare_rho+nonmin_rho,bare_p+nonmin_p,
                       bare_rho,bare_p,nonmin_rho,nonmin_p)


def dynamics(H, b, v, m2=0, lam=0):
    """Return dot(b), dot(v). Exact O(3)-invariant 2-form Euler equation."""
    H,b,v=map(q,(H,b,v));m2,lam=_safe_params(m2,lam)
    return v-2*H*b, -H*v-(m2-2*lam*H*H)*b


def continuity_residual(H, hdot, b, v, m2=0, lam=0):
    """dot(rho)+3H(rho+p) evaluated with the 2-form Euler equation."""
    H,hdot,b,v=map(q,(H,hdot,b,v));m2,lam=_safe_params(m2,lam)
    bd,vd=dynamics(H,b,v,m2,lam)
    drho=3*v*vd+3*m2*b*bd + 6*lam*H*hdot*b*b+6*lam*H*H*b*bd
    r=stress(H,hdot,b,v,m2,lam)
    return drho+3*H*(r.rho+r.pressure)


def tetrad_bivectors(e,b,count=3):
    """Bivector components in pairs (01,02,03,23,31,12), orthonormal.

    For each copy a, electric and magnetic spatial directions use the SAME
    internal index.  When both e and b are nonzero, E/B mixing is present.
    """
    if type(count) is not int or count not in (1,2,3):
        raise ValueError('only 1, 2 or 3 aligned species')
    e,b=map(q,(e,b))
    ans=[]
    for a in range(count):
        t=[F(0)]*6
        t[a]=e
        t[a+3]=b
        ans.append(tuple(t))
    return tuple(ans)


def response_matrix(species):
    """Sum_a B^a_P B^a_Q, six-by-six symmetric covariant pair Gram.

    It is NOT the full GfE induced operator. In a two-form curvature coupling,
    lambda/4 times this Gram is the response to the independent pair-curvature
    block at fixed field and metric, prior to enforcing Riemann Bianchi rules.
    """
    species=tuple(tuple(map(q,b)) for b in species)
    if any(len(b)!=6 for b in species):raise ValueError('six antisymmetric pairs')
    return tuple(tuple(sum((b[i]*b[j] for b in species),F(0))
                      for j in range(6)) for i in range(6))


def diagonal_block_test(M):
    """Return (E coefficient,B coefficient,cross coefficient) if isotropic.

    A scalar E/B cross term is rotationally invariant but spoils a diagonal
    tensor-sector ansatz. Values may be nonzero in both blocks.
    """
    if len(M)!=6 or any(len(row)!=6 for row in M):raise ValueError('6 by 6')
    e,b,c=M[0][0],M[3][3],M[0][3]
    for i in range(3):
        for j in range(3):
            u=F(1) if i==j else F(0)
            if M[i][j]!=e*u or M[i+3][j+3]!=b*u or M[i][j+3]!=c*u or M[i+3][j]!=c*u:
                return None
    return e,b,c


def rank_q(A):
    """Exact Gaussian elimination rank over rational numbers."""
    mat=[list(map(q,row)) for row in A]
    if not mat: return 0
    n=len(mat);m=len(mat[0]);r=0
    if any(len(row)!=m for row in mat):raise ValueError('ragged matrix')
    for j in range(m):
        pivot=next((i for i in range(r,n) if mat[i][j]),None)
        if pivot is None:continue
        mat[r],mat[pivot]=mat[pivot],mat[r]
        v=mat[r][j]
        mat[r]=[u/v for u in mat[r]]
        for i in range(n):
            if i!=r and mat[i][j]:
                t=mat[i][j]
                mat[i]=[a-t*b for a,b in zip(mat[i],mat[r])]
        r+=1
        if r==n:break
    return r


def four_tensor_response(b, lam):
    """P^{ijkl}=lambda/4*b²*(delta_ik delta_jl-delta_il delta_jk).

    Returns 4^4 covariant tetrad components, zero in every temporal slot.
    For the pure-magnetic triad this already has algebraic Riemann symmetries.
    """
    b,lam=map(q,(b,lam))
    return tuple(tuple(tuple(tuple(
        lam*b*b*F((i==k)*(j==l)-(i==l)*(j==k),4)
        if min(i,j,k,l)>=1 else F(0)
        for l in range(4)) for k in range(4)) for j in range(4)) for i in range(4))


def flrw_curvature_response(H,hdot,b,lam):
    """P:R for the pure-magnetic triad on flat FLRW, exact 4-index sum."""
    H,hdot=map(q,(H,hdot))
    P=four_tensor_response(b,lam)
    # R_{ijkl}=H²(delta_ik delta_jl-delta_il delta_jk) tetrad components
    # and R_{0i0j}=-(Hdot+H²)delta_ij, which P cannot sample.
    return sum((P[i][j][k][l]*H*H*((i==k)*(j==l)-(i==l)*(j==k))
                for i in range(4) for j in range(4) for k in range(4) for l in range(4)),F(0))


def target_b2(beta,alpha,chi,hdot):
    """Cone matching mE=0, mB=chi*b²: b²=-2 beta Hdot/(alpha chi)."""
    beta,alpha,chi,hdot=map(q,(beta,alpha,chi,hdot))
    if min(beta,alpha,chi)<=0:raise ValueError('positive couplings required')
    return -2*beta*hdot/(alpha*chi)


def match_gap(beta,alpha,chi,H,hdot,b):
    """theta_E-theta_B for a diagonal E/B constitutive extension."""
    beta,alpha,chi,H,hdot,b=map(q,(beta,alpha,chi,H,hdot,b))
    if min(beta,alpha,chi)<=0:raise ValueError('positive couplings required')
    return -alpha*chi*b*b-2*beta*hdot


def matching_constraint(H,hdot,hddot,htriple,m2,lam):
    """Third-order H constraint for a nonzero b with b² proportional -Hdot.

    Derived by differentiating b²=-c Hdot and imposing the triad EOM.
    Valid on Hdot<0, b!=0; the normalization c cancels.
    """
    H,hdot,hddot,htriple,m2,lam=map(q,(H,hdot,hddot,htriple,m2,lam))
    if hdot>=0:raise ValueError('matching branch requires negative Hdot')
    if m2<0:raise ValueError('negative mass squared')
    return (htriple/(2*hdot)-hddot*hddot/(4*hdot*hdot)+2*hdot
           +3*H*hddot/(2*hdot)+2*H*H +m2-2*lam*H*H)


def powerlaw_reduced_condition(power,m2,lam,time):
    """EOM/b for b=c/t on H=power/t under cone matching.

    (p-2)(2p-1)-2lambda p² + m² t² = 0 is required at every time.
    """
    power,m2,lam,time=map(q,(power,m2,lam,time))
    if time<=0 or m2<0:raise ValueError('time positive, mass² nonnegative')
    return (power-2)*(2*power-1)-2*lam*power*power+m2*time*time


def constrained_kinetic_hessian(a,N,w,lam,planck_sq=0):
    """Homogeneous velocity Hessian for matter plus EH minisuperspace term.

    In coordinate field w=a² b, L=3 dot(w)^2/(2Na)-3Nm²w²/(2a)
    +3lam dot(a)^2 w²/(Na³)-3M_P² a dot(a)^2/N.  H_aa,H_ww.
    This is NOT the 4D coupled tensor principal symbol.
    """
    a,N,w,lam,planck_sq=map(q,(a,N,w,lam,planck_sq))
    if a<=0 or N<=0 or planck_sq<0:raise ValueError('invalid homogeneous parameters')
    return ((6*lam*w*w/(N*a**3)-6*planck_sq*a/N,F(0)),
            (F(0),3/(N*a)))


def schur_2x2(a,b,c):
    """Generic two-field principal-block Schur identity, c nonzero."""
    a,b,c=map(q,(a,b,c))
    if not c:raise ValueError('invertible second block required')
    return a-b*b/c,(a*c-b*b)/c




def evolve_powerlaw(power, b0, v0, m2=0, lam=0, *, t0=1., t1=2., steps=500):
    """RK4 spectator 2-form evolution on H(t)=power/t, with fixed geometry.

    Illustrative background is externally prescribed; it does not solve the
    full Einstein/GfE system. Use analytical exact functions above for proof.
    """
    power,b0,v0,m2,lam = map(float,(power,b0,v0,m2,lam))
    if type(steps) is not int or steps<1 or t0<=0 or t1<=t0 or m2<0:
        raise ValueError('invalid integration domain')
    step=(t1-t0)/steps
    b,v=b0,v0
    def rhs(time,B,V):
        H=power/time
        return V-2*H*B, -H*V-(m2-2*lam*H*H)*B
    for k in range(steps):
        t=t0+k*step
        b1,v1=rhs(t,b,v)
        b2,v2=rhs(t+step/2,b+step*b1/2,v+step*v1/2)
        b3,v3=rhs(t+step/2,b+step*b2/2,v+step*v2/2)
        b4,v4=rhs(t+step,b+step*b3,v+step*v3)
        b+=step*(b1+2*b2+2*b3+b4)/6
        v+=step*(v1+2*v2+2*v3+v4)/6
    return {'time':t1,'b':b,'v':v,
            'matching_error':b*b-(b0*t0/t1)**2}

def reference_receipt():
    from itertools import product
    b=F(1);H=F(2);hdot=F(-1,4);qval=F(3)
    s=stress(H,hdot,b,qval,F(1,5),F(1,10))
    g=response_matrix(tetrad_bivectors(0,b,3))
    return {'schema':'mathcan.toe08.triad.v1',
            'source':'MathCan-defined massive 2-form triad with RBB coupling',
            'rho':str(s.rho),'pressure':str(s.pressure),
            'continuity_residual':str(continuity_residual(H,hdot,b,qval,F(1,5),F(1,10))),
            'response_rank':rank_q(g),
            'curvature_response_scalar':str(flrw_curvature_response(H,hdot,b,F(1,10))),
            'pure_massless_powers':['1/2','2'],
            'isolated_coupled_tensor_symbol':'not derived'}


if __name__=='__main__':
    import json
    print(json.dumps(reference_receipt(),sort_keys=True,indent=2))
