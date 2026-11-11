"""TOE-07: exact rational algebraic two-response tensor-cone diagnostic.

Motivation: Pereira, arXiv:2609.03082, strict-principal TT polynomial and
isotropic E/B curvature-response compensation condition. The two tunable
parameters in this module are effective isotropic 2-form source responses,
NOT an explicit solution to a two-multiplet field action. Such a solution,
including matter dynamics and full finite-frequency hyperbolicity, is open.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Iterable


def rat(value):
    if type(value) is bool:
        raise ValueError('boolean is not a field parameter')
    return Q(value)


@dataclass(frozen=True)
class Cone:
    ws: Q
    we: Q
    wb: Q
    theta_e: Q
    theta_b: Q
    response_split: Q
    discriminant: Q
    characteristic_at_lightcone: Q

    @property
    def real_strict_principal_characteristic(self):
        return self.discriminant == 0


def target_matter_split(beta, alpha, hdot, k_over_a2=0):
    """Required isotropic source E-B response difference for equal theta.

    theta_E=1+alpha*m_E-2*beta*(H**2+hdot)
    theta_B=1+alpha*m_B-2*beta*(H**2+k_over_a2).
    """
    beta, alpha, hdot, k_over_a2 = map(rat,(beta,alpha,hdot,k_over_a2))
    if beta <= 0 or alpha <= 0:
        raise ValueError('positive couplings required')
    return 2*beta*(hdot-k_over_a2)/alpha


def nonnegative_algebraic_compensation(beta, alpha, hdot, k_over_a2=0, baseline=0):
    """Two nonnegative effective response numbers satisfying matching exactly.

    This is a pointwise algebraic construction. It does not construct physical
    two-form tensors, two Dirac-Kahler multiplets or matter field equations.
    """
    d=target_matter_split(beta,alpha,hdot,k_over_a2)
    baseline=rat(baseline)
    if baseline<0:raise ValueError('baseline must be nonnegative')
    return baseline+max(d,Q(0)),baseline+max(-d,Q(0))


def cone(beta,alpha,H,hdot,mE=0,mB=0,k_over_a2=0):
    beta,alpha,H,hdot,mE,mB,k_over_a2=map(rat,
        (beta,alpha,H,hdot,mE,mB,k_over_a2))
    if beta<=0 or alpha<=0 or mE<0 or mB<0:
        raise ValueError('invalid positive couplings or negative effective responses')
    A=H*H+hdot; B=H*H+k_over_a2
    theta_s=1-beta*(A+2*B)
    theta_e=1+alpha*mE-2*beta*A
    theta_b=1+alpha*mB-2*beta*B
    if min(theta_s,theta_e,theta_b)<=0:
        raise ValueError('nonpositive G-field tensor-sector eigenvalue')
    ws,we,wb=1/theta_s,1/theta_e,1/theta_b
    disc=-4*ws**2*(we-wb)**2
    split=alpha*(mE-mB)-2*beta*(hdot-k_over_a2)
    assert theta_e-theta_b == split
    assert we-wb == -split/(theta_e*theta_b)
    assert disc == -4*ws**2*split**2/(theta_e**2*theta_b**2)
    return Cone(ws,we,wb,theta_e,theta_b,split,disc,2*(we-wb)**2)


def principal_q4(c:Cone,omega_sq=1,p_sq=1):
    omega_sq,p_sq=map(rat,(omega_sq,p_sq))
    if p_sq<=0 or omega_sq<0:raise ValueError('nonnegative squared frequency, positive p2')
    return c.ws**2/Q(2)*(omega_sq-p_sq)**2+2*(c.we*omega_sq-c.wb*p_sq)**2


def wedge_oneforms(a:Iterable,b:Iterable):
    """Antisymmetric wedge on R^4, ordered 01,02,03,12,13,23."""
    a=tuple(map(rat,a));b=tuple(map(rat,b))
    if len(a)!=4 or len(b)!=4:raise ValueError('four-dimensional one-forms required')
    return tuple(a[i]*b[j]-a[j]*b[i]
                 for i,j in ((0,1),(0,2),(0,3),(1,2),(1,3),(2,3)))


def homogeneous_scalar_wedge(pi1,pi2):
    return wedge_oneforms((rat(pi1),0,0,0),(rat(pi2),0,0,0))


def trajectory_diagnostic(curve,beta=Q(1,100),alpha=Q(3,50)):
    """Algebraic E/B compensation along existing *synthetic* TOE-05 curve."""
    out=[]
    for p in curve:
        H=rat(str(p['H'])); hdot=rat(str(p['Hdot']))
        mE,mB=nonnegative_algebraic_compensation(beta,alpha,hdot)
        old=cone(beta,alpha,H,hdot)
        patched=cone(beta,alpha,H,hdot,mE,mB)
        assert patched.real_strict_principal_characteristic
        assert not old.real_strict_principal_characteristic if hdot!=0 else True
        out.append({'z':p['z'],'Hdot':p['Hdot'],
                    'mE':str(mE),'mB':str(mB),'theta_E':float(patched.theta_e),
                    'theta_B':float(patched.theta_b),
                    'uncompensated_discriminant':float(old.discriminant),
                    'compensated_discriminant':str(patched.discriminant)})
    return out


def vector_response(vectors):
    """Rank-one outer-product sum of spatial E or B vectors, 3x3 rational.

    One two-form contributes one electric and one magnetic 3-vector.
    Isotropy of each sector separately is a stronger requirement than
    isotropy of a combined E+B quadratic sum.
    """
    vs=[tuple(map(rat,v)) for v in vectors]
    if any(len(v)!=3 for v in vs):raise ValueError('three spatial components required')
    return tuple(tuple(sum((v[i]*v[j] for v in vs),Q(0)) for j in range(3)) for i in range(3))


def det3(M):
    if len(M)!=3 or any(len(x)!=3 for x in M):raise ValueError('3x3 matrix expected')
    a,b,c=M[0];d,e,f=M[1];g,h,i=M[2]
    return a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)


def scalar_isotropic(M):
    return all(M[i][j]==(M[0][0] if i==j else 0) for i in range(3) for j in range(3))
