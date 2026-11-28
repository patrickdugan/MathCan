"""DEL-12: independent exact sparse-polynomial partial derivative oracle.

Uses polynomial coefficient dictionaries over finite fields. The derivatives
are calculated from monomial exponents and ring arithmetic, independently
of DEL-11's declared gradient functions.

No scheme-level smoothness theorem is inferred from finite evaluations.
"""
from research.deligne_sign_audit.prime_power_fourier import FIELDS


def normalize(field,terms):
    d={}
    for c,monomial in terms:
        exps=tuple(monomial)
        if len(exps)!=2 or any(e<0 for e in exps):
            raise ValueError("conic polynomial expects two nonnegative exponents")
        d[exps]=field.add(d.get(exps,0),c)
    return {k:v for k,v in d.items() if v!=0}


def conic_polynomial(field,a,b,c):
    return normalize(field,[
        (1,(1,1)),(a,(1,0)),(b,(0,1)),(c,(0,0))
    ])


def evaluate(field,P,x,y):
    z=0
    for (p,q),coefficient in P.items():
        z=field.add(z,field.mul(coefficient,
                        field.mul(field.pow(x,p),field.pow(y,q))))
    return z


def pderiv(field,P,axis):
    if axis not in (0,1):
        raise ValueError("coordinate axis must be 0 or 1")
    terms=[]
    for exps,coeff in P.items():
        m=exps[axis]
        if m==0:
            continue
        new=tuple(d-int(i==axis) for i,d in enumerate(exps))
        terms.append((field.mul(coeff,m%field.p),new))
    return normalize(field,terms)


def derivative_conic_certificate(field,a,b,c,x,y):
    P=conic_polynomial(field,a,b,c)
    dx=pderiv(field,P,0)
    dy=pderiv(field,P,1)
    predicted_dx=normalize(field,[(1,(0,1)),(a,(0,0))])
    predicted_dy=normalize(field,[(1,(1,0)),(b,(0,0))])
    return {
      "P":P,"dx":dx,"dy":dy,
      "symbolic_dx_ok":dx==predicted_dx,
      "symbolic_dy_ok":dy==predicted_dy,
      "value":evaluate(field,P,x,y),
      "dx_value":evaluate(field,dx,x,y),
      "dy_value":evaluate(field,dy,x,y),
      "expected_dx":field.add(y,a),
      "expected_dy":field.add(x,b),
    }


def discriminant(field,a,b,c):
    return field.sub(c,field.mul(a,b))


def critical_point(field,a,b,c):
    x,y=field.neg(b),field.neg(a)
    r=derivative_conic_certificate(field,a,b,c,x,y)
    assert r["dx_value"]==r["dy_value"]==0
    assert r["value"]==discriminant(field,a,b,c)
    return x,y,r


def inseparable_frobenius_square(field,c):
    """X^p + c in characteristic p has identically zero d/dX."""
    P=normalize(field,[(1,(field.p,0)),(c,(0,0))])
    dx=pderiv(field,P,0)
    assert not dx
    return P,dx


def tangent_line_counterexample(field):
    """F=xy+1, line y=x-2 through (1,-1), restricted equation
    (x-1)^2. The ambient gradient is nonzero while the
    restriction's derivative vanishes."""
    one,two=1,field.add(1,1)
    y=field.sub(one,two)
    P=conic_polynomial(field,0,0,one)
    full=derivative_conic_certificate(field,0,0,one,one,y)
    restricted=field.add(field.mul(one,y),one)
    slope_derivative=field.sub(field.add(one,one),two)
    return {
      "ambient_on_level":full["value"]==0,
      "ambient_gradient_nonzero":bool(full["dx_value"] or full["dy_value"]),
      "line_contains_point":y==field.sub(one,two),
      "restricted_point_on_level":restricted==0,
      "restricted_derivative_zero":slope_derivative==0,
    }
