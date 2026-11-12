"""TOE-12: exact auxiliary 2-form G-field inverse-map linearization.

This is the algebraic induced-metric relation in a *declared non-Abelian*
2-form extension, on invertible 6x6 matrices. It leaves the complete source
0/1-form channels and covariant derivative/stress variation outstanding.
"""
from __future__ import annotations
from fractions import Fraction as Q
from .operator_principal import (
    colored_background,build_theta,differential,identity,inverse,mul,zeros,
)
from .jordan_principal import add,mm


def response_first(theta, delta_theta):
    """DG = -Theta^-1 (DTheta) Theta^-1, full noncommuting 6x6 exact."""
    if len(theta)!=6 or len(delta_theta)!=6:
        raise ValueError('six-dimensional 2-form operators only')
    G=inverse(theta)
    return add(zeros(),mm(mm(G,delta_theta),G),kb=-1)


def exact_resolvent(theta,delta_theta,dt):
    """Exact quadratic remainder for the linearized auxiliary relation."""
    dt=Q(dt)
    if not dt:raise ValueError('nonzero finite variation required')
    G=inverse(theta)
    DG=response_first(theta,delta_theta)
    GT=inverse(add(theta,delta_theta,kb=dt))
    remainder=add(GT,add(G,DG,kb=dt),kb=-1)
    rhs=mm(mm(mm(mm(G,delta_theta),G),delta_theta),GT)
    rhs=add(zeros(),rhs,kb=dt*dt)
    if remainder!=rhs:raise AssertionError('resolvent identity')
    return {'G':G,'first':DG,'second_order_remainder':remainder,
            'resolvent_quadratic_identity':True}


def trial_response(electric=(2,Q(1001,1000)),magnetic=(1,0),
                   A=Q(2,5),Bcurv=1,alpha=Q(3,500),beta=Q(1,100)):
    F=colored_background(electric,magnetic)
    theta=build_theta(F,A,Bcurv,alpha,beta)
    # Change one flavor/color in the transverse gauge tensor; a separate
    # physical perturbation requires its wave-covector realization.
    df=[(Q(),)*6 for _ in F]
    df[0]=(Q(1),Q(),Q(),Q(),Q(),Q())
    df=tuple(df)
    R=tuple(tuple(Q(1 if i==j==0 else 0) for j in range(6)) for i in range(6))
    PR,PF,_=differential(F,df,R,alpha,beta)
    return theta,add(PR,PF)


def reference_example():
    t,d=trial_response()
    v=exact_resolvent(t,d,Q(1,1000))
    nonzero=sum((x!=0 for row in v['first'] for x in row))
    return {'schema':'mathcan.toe12.auxiliary_2form.v1',
            'nonzero_first_variation_entries':nonzero,
            'exact_resolvent_quadratic_identity':True,
            'algebraically_eliminated_G2form':True,
            'full_Gfield_and_metric_equations_verified':False}

if __name__=='__main__':
    import json
    print(json.dumps(reference_example(),indent=2))
