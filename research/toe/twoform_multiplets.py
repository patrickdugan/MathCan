"""TOE-08B: two O(3) magnetic two-form triads and an exact flavor-area obstruction.

Each 'multiplet' here is an SO(3) triplet of independent 2-form potentials
with the action in TOE08_TWOFORM_TRIAD_ACTION.md. This is a MathCan trial
field content, not a claim that two Dirac--Kahler multiplets have been solved.
Exact rational algebra and a separately labelled spectator RK4 integrator.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F

from .twoform_triad import q, stress


@dataclass(frozen=True)
class TwoTriadState:
    b1: F
    b2: F
    v1: F
    v2: F

    def __post_init__(self):
        for key in ('b1','b2','v1','v2'):
            object.__setattr__(self, key, q(getattr(self, key)))


def invariants(s: TwoTriadState):
    """Magnetic amplitude S, radial momentum Q, and flavor wedge W."""
    S = s.b1*s.b1 + s.b2*s.b2
    Q = s.b1*s.v1 + s.b2*s.v2
    W = s.b1*s.v2 - s.b2*s.v1
    return S, Q, W


def rhs(H, s: TwoTriadState, m2_1=0, lam1=0, m2_2=0, lam2=0):
    """(b_dot1,b_dot2,v_dot1,v_dot2) for the concrete 2-form actions."""
    H, m2_1, lam1, m2_2, lam2 = map(q,(H,m2_1,lam1,m2_2,lam2))
    if m2_1 < 0 or m2_2 < 0:
        raise ValueError('nonnegative two-form masses required')
    M1 = m2_1 - 2*lam1*H*H
    M2 = m2_2 - 2*lam2*H*H
    return (s.v1 - 2*H*s.b1, s.v2 - 2*H*s.b2,
            -H*s.v1 - M1*s.b1, -H*s.v2 - M2*s.b2)


def invariant_derivatives(H, hdot, s: TwoTriadState,
                          m2_1=0, lam1=0, m2_2=0, lam2=0):
    """Analytic S', S'', Q', W' with independent couplings, exact Fraction."""
    H,hdot,m2_1,lam1,m2_2,lam2 = map(q,(H,hdot,m2_1,lam1,m2_2,lam2))
    if min(m2_1,m2_2)<0: raise ValueError('nonnegative masses')
    S,Q,W=invariants(s)
    M1=m2_1-2*lam1*H*H
    M2=m2_2-2*lam2*H*H
    qs=s.v1*s.v1+s.v2*s.v2
    mass=M1*s.b1*s.b1+M2*s.b2*s.b2
    Sd=2*Q-4*H*S
    Qd=qs-3*H*Q-mass
    Wd=-3*H*W+(M1-M2)*s.b1*s.b2
    Sdd=2*Qd-4*hdot*S-4*H*Sd
    return {'S':S,'Q':Q,'W':W,'Sdot':Sd,'Sddot':Sdd,
            'Qdot':Qd,'Wdot':Wd,'mass_weight':mass,
            'sum_v2':qs}


def lagrange_gap(s: TwoTriadState):
    """Lagrange identity S*sum(v²) - Q² = W² in two species."""
    S,Q,W=invariants(s)
    return S*(s.v1*s.v1+s.v2*s.v2)-Q*Q-W*W


def radial_certificate(H, hdot, s: TwoTriadState,
                       m2_1=0, lam1=0, m2_2=0, lam2=0):
    """Exact two-triad curvature/matter compatibility identity for S>0.

    Sddot+7H*Sdot+(12H²+4Hdot)S+2ΣM_i b_i² =
      [ (Sdot+4HS)²+4W² ]/(2S).
    The positive W term measures flavor orientation motion. Its omission
    would mistake a two-field trajectory for a single radial field.
    """
    d=invariant_derivatives(H,hdot,s,m2_1,lam1,m2_2,lam2)
    S=d['S']
    if S<=0:raise ValueError('nonzero two-triad amplitude required')
    H,hdot=map(q,(H,hdot))
    lhs=d['Sddot']+7*H*d['Sdot']+(12*H*H+4*hdot)*S+2*d['mass_weight']
    rhs=((d['Sdot']+4*H*S)**2+4*d['W']**2)/(2*S)
    return {'lhs':lhs,'rhs':rhs,'gap':lhs-rhs,
            'flavor_term':2*d['W']**2/S}


def cone_gap(beta,alpha,chi,hdot,s:TwoTriadState):
    """Conditional TOE-07 magnetic constitutive law m_B=chi*(b1²+b2²)."""
    beta,alpha,chi,hdot=map(q,(beta,alpha,chi,hdot))
    if min(beta,alpha,chi)<=0:raise ValueError('positive response couplings')
    S,_,_=invariants(s)
    return -alpha*chi*S-2*beta*hdot


def total_stress(H, hdot, s:TwoTriadState,
                 m2_1=0,lam1=0,m2_2=0,lam2=0):
    a=stress(H,hdot,s.b1,s.v1,m2_1,lam1)
    b=stress(H,hdot,s.b2,s.v2,m2_2,lam2)
    return (a.rho+b.rho,a.pressure+b.pressure)


def spectator_powerlaw(power, s0:TwoTriadState, *, m2_1=0,lam1=0,
                       m2_2=0,lam2=0,t0=1.0,t1=2.0,steps=600):
    """Two triad ODE on prescribed a(t)~t^p; no gravitational backreaction."""
    power,m2_1,lam1,m2_2,lam2 =map(float,(power,m2_1,lam1,m2_2,lam2))
    if type(steps)!=int or steps<1 or t0<=0 or t1<=t0:raise ValueError('invalid range')
    if min(m2_1,m2_2)<0:raise ValueError('negative mass squared')
    y=[float(x) for x in (s0.b1,s0.b2,s0.v1,s0.v2)]
    def f(t, vec):
        h=power/t
        m1=m2_1-2*lam1*h*h; m2=m2_2-2*lam2*h*h
        b1,b2,v1,v2=vec
        return [v1-2*h*b1,v2-2*h*b2,-h*v1-m1*b1,-h*v2-m2*b2]
    h=(t1-t0)/steps
    for i in range(steps):
        t=t0+i*h
        k1=f(t,y)
        k2=f(t+h/2,[z+h*u/2 for z,u in zip(y,k1)])
        k3=f(t+h/2,[z+h*u/2 for z,u in zip(y,k2)])
        k4=f(t+h,[z+h*u for z,u in zip(y,k3)])
        y=[z+h*(u+2*v+2*w+x)/6
           for z,u,v,w,x in zip(y,k1,k2,k3,k4)]
    b1,b2,v1,v2=y
    return {'time':t1,'b1':b1,'b2':b2,'v1':v1,'v2':v2,
            'S':b1*b1+b2*b2,'W':b1*v2-b2*v1}


def exact_powerlaw_twofield(time):
    """An analytic m=lambda=0, a=t² two-triad solution with flavor rotation.

    b1=1/t, v1=3/t²; b2=(t³-1)/(6t⁴), v2=1/(2t²).
    At t=1, cone response S=b1²+b2² matches 1/t², but for any t>1
    the extra b2² makes S strictly larger. This does not solve Einstein/GfE.
    """
    t=q(time)
    if t<=0:raise ValueError('positive time required')
    return TwoTriadState(1/t,(t**3-1)/(6*t**4),3/t**2,1/(2*t**2))


def homogeneous_two_kinetic(a,N,w1,w2,lam1,lam2,planck_sq):
    """Exact (a,w1,w2) velocity Hessian for two triads plus EH kinetic term.

    Only a homogeneous Hessian, not the full metric--matter wave operator.
    The Einstein conformal variable's coefficient can vanish on
    lam1*(w1/a²)²+lam2*(w2/a²)²=M_P².
    """
    a,N,w1,w2,lam1,lam2,planck_sq=map(q,(a,N,w1,w2,lam1,lam2,planck_sq))
    if min(a,N)<=0 or planck_sq<0:raise ValueError('invalid scale/lapse/Mp²')
    grav=6*(lam1*w1*w1+lam2*w2*w2)/(N*a**3)-6*planck_sq*a/N
    matter=3/(N*a)
    return ((grav,F(0),F(0)),(F(0),matter,F(0)),(F(0),F(0),matter))
