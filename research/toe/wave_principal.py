"""TOE-11: one gauge/metric tensor-mode projection of the declared 2-form symbol.

Frozen local orthonormal background. Wave covector (omega,0,0,1).
The metric mode is h_xx=-h_yy, the gauge spin-2 perturbation has
 a_x^(flavor0,color0)=+1, a_y^(flavor0,color1)=-1.
The reduced 2x principal quadratic form has polynomial degrees 4,3,2 in
omega for metric-metric, metric-gauge, gauge-gauge entries respectively.

This *restricted two-form plus YM symbol* excludes gravity's 0- and 1-form
sectors, the independent G-field, the other gauge polarizations, and all
constraints. Repeated roots are not evidence for strong hyperbolicity.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from .operator_principal import (
    colored_background, wave_riemann_pair, wave_field_strength,
    susceptibility,
)
from .mixed_principal import rat


def metric_tt():
    return tuple(tuple(Q(1 if i==j==1 else -1 if i==j==2 else 0)
                       for j in range(4)) for i in range(4))


def amplitudes(omega, nflavor):
    xi=(rat(omega),Q(),Q(),Q(1))
    dF=[]
    for f in range(nflavor):
        for adj in range(3):
            v=(0,0,0,0)
            if f==0 and adj==0:v=(0,1,0,0)
            if f==0 and adj==1:v=(0,0,-1,0)
            dF.append(wave_field_strength(xi,v))
    return wave_riemann_pair(xi,metric_tt()),tuple(dF)


def evaluate_polynomial(coeff,x):
    x=rat(x)
    return sum((v*x**i for i,v in enumerate(coeff)),Q())


def symbol_at(omega, *, electric,magnetic,A,Bcurv,alpha,beta,sigma):
    E=tuple(map(rat,electric));B=tuple(map(rat,magnetic))
    dr,df=amplitudes(omega,len(E))
    F=colored_background(E,B)
    return susceptibility(F,df,dr,A=A,B=Bcurv,alpha=alpha,beta=beta,sigma=sigma)


@dataclass(frozen=True)
class RestrictedSymbol:
    rr:tuple[Q,Q,Q]
    rf:tuple[Q,Q]
    ff:tuple[Q,Q]
    determinant:tuple[Q,Q,Q,Q]
    doubled_gravity_root:Q
    remaining_linear_factor:tuple[Q,Q]

    def at(self,omega):
        w=rat(omega)
        return (evaluate_polynomial(self.rr,w*w),
                w*evaluate_polynomial(self.rf,w*w),
                evaluate_polynomial(self.ff,w*w))

    def det_at(self,omega):
        r,m,g=self.at(omega)
        return r*g-m*m

    def remaining_root(self):
        a,b=self.remaining_linear_factor
        if b==0:return None
        return -a/b


def construct_symbol(*,electric,magnetic,A,Bcurv,alpha,beta,sigma):
    kw=dict(electric=electric,magnetic=magnetic,A=A,Bcurv=Bcurv,
            alpha=alpha,beta=beta,sigma=sigma)
    z=symbol_at(0,**kw)
    u=symbol_at(1,**kw)
    v=symbol_at(2,**kw)
    # rr=rr0+rr2*w²+rr4*w^4; rf=w*(rf1+rf3*w²); ff=ff0+ff2*w²
    rr0=z['rr'];r4=(v['rr']-4*u['rr']+3*rr0)/12
    r2=u['rr']-rr0-r4
    m3=(v['rf']/2-u['rf'])/3
    m1=u['rf']-m3
    f0=z['ff'];f2=u['ff']-f0
    rr=(rr0,r2,r4);rf=(m1,m3);ff=(f0,f2)
    det=(r2*f0+rr0*f2-m1*m1,
         r4*f0+r2*f2-2*m1*m3,
         r4*f2-m3*m3)
    coefficients=(rr0*f0,*det)
    # Test degree/parity by independently executing the 6x susceptibility.
    for w in (-3,-2,-1,0,1,2,3):
        result=symbol_at(w,**kw)
        observed=(result['rr'],result['rf'],result['ff'])
        predicted=(evaluate_polynomial(rr,w*w),
                   w*evaluate_polynomial(rf,w*w),
                   evaluate_polynomial(ff,w*w))
        assert observed==predicted
    a=rat(alpha);b=rat(beta);A=rat(A);Bcurv=rat(Bcurv)
    E=tuple(map(rat,electric));BB=tuple(map(rat,magnetic))
    thetaE=1-a*sum((v*v for v in E),Q())-2*b*A
    thetaB=1+a*sum((v*v for v in BB),Q())-2*b*Bcurv
    if thetaE<=0 or thetaB<=0:raise ValueError('positive diagonal baseline required')
    root=thetaE/thetaB
    if evaluate_polynomial(coefficients,root)!=0 or (
            coefficients[1]+2*coefficients[2]*root+3*coefficients[3]*root**2)!=0:
        raise ValueError('doubled root fails in this restricted projection')
    # Exact polynomial quotient by (x-root)^2
    bfactor=coefficients[3]
    afactor=coefficients[2]+2*root*bfactor
    assert tuple(coefficients)==(afactor*root**2,
                   bfactor*root**2-2*afactor*root,
                   afactor-2*bfactor*root,
                   bfactor)
    return RestrictedSymbol(rr,rf,ff,coefficients,root,(afactor,bfactor))


def example():
    s=construct_symbol(electric=(2,Q(1001,1000)),magnetic=(1,0),
                       A=Q(2,5),Bcurv=1,alpha=Q(3,500),
                       beta=Q(1,100),sigma=Q(1,100))
    return {'schema':'mathcan.toe11.projected_wave.v1',
            'scope':'single TT metric and single gauge tensor amplitude, declared 2-form plus YM only',
            'doubled_gravitational_speed_squared':str(s.doubled_gravity_root),
            'remaining_speed_squared':str(s.remaining_root()),
            'sextic_polynomial_coefficients':list(map(str,s.determinant)),
            'mixed_cubic_coefficients':list(map(str,s.rf)),
            'all_positive_roots':s.doubled_gravity_root>0 and s.remaining_root()>0,
            'strong_hyperbolicity_verified':False}

if __name__=='__main__':
    import json
    print(json.dumps(example(),indent=2))
