"""DEL-13 exact polynomial Bézout and global Jacobian ideal oracle.

For the actual conic polynomial F=XY+aX+bY+c, the polynomial identity
    F - (dF/dY)*(dF/dX) = c - ab
is checked by direct coefficient arithmetic in F_q[X,Y].
When c-ab is nonzero, multiplication by its inverse produces 1 in the
Jacobian ideal. When c-ab vanishes, the singular point (-b,-a) defines
an evaluation homomorphism annihilating every ideal generator.
This is a finite-field shadow of the pinned Lean theorem.
"""
from research.deligne_sign_audit.del12_oracle import (
    normalize, conic_polynomial, pderiv, evaluate,
)
from research.deligne_sign_audit.prime_power_fourier import FIELDS


def poly_add(field,A,B):
    terms=[(c,e) for e,c in A.items()]+[(c,e) for e,c in B.items()]
    return normalize(field,terms)


def poly_neg(field,A):
    return normalize(field,[(field.neg(c),e) for e,c in A.items()])


def poly_sub(field,A,B):
    return poly_add(field,A,poly_neg(field,B))


def poly_mul(field,A,B):
    terms=[]
    for (p,q),c in A.items():
        for (r,s),d in B.items():
            terms.append((field.mul(c,d),(p+r,q+s)))
    return normalize(field,terms)


def poly_scalar(field,k,A):
    return normalize(field,[(field.mul(k,c),e) for e,c in A.items()])


def constant(field,c):
    return normalize(field,[(c,(0,0))])


def conic_bezout(field,a,b,c):
    F=conic_polynomial(field,a,b,c)
    dx=pderiv(field,F,0)
    dy=pderiv(field,F,1)
    delta=field.sub(c,field.mul(a,b))
    left=poly_sub(field,F,poly_mul(field,dy,dx))
    return {
        "F":F,"dx":dx,"dy":dy,"delta":delta,"lhs":left,
        "rhs":constant(field,delta),
        "identity":left==constant(field,delta),
    }


def conic_unit_certificate(field,a,b,c):
    result=conic_bezout(field,a,b,c)
    delta=result["delta"]
    if delta==0:
        return None
    k=field.inv(delta)
    left=poly_scalar(field,k,result["lhs"])
    return {
        "inverse":k,
        "unit_identity":left==constant(field,1),
        "constant":left,
        "delta":delta,
        "coeffs":{
            "F":constant(field,k),
            "dx":poly_neg(field,poly_mul(field,constant(field,k),result["dy"])),
            "dy":{}
        },
    }


def singular_ideal_obstruction(field,a,b,c):
    out=conic_bezout(field,a,b,c)
    x,y=field.neg(b),field.neg(a)
    values=tuple(evaluate(field,P,x,y) for P in
                  (out["F"],out["dx"],out["dy"]))
    return {
        "delta":out["delta"],
        "singular_point":(x,y),
        "all_generators_zero":all(z==0 for z in values),
        "generator_evaluations":values,
        "certificate_exists":conic_unit_certificate(field,a,b,c) is not None,
    }


def wrong_sign_certificate(field,a,b,c):
    return field.add(c,field.mul(a,b))


def swapped_factor_certificate(field,a,b,c):
    F=conic_polynomial(field,a,b,c)
    dx=pderiv(field,F,0)
    wrong=poly_sub(field,F,poly_mul(field,dx,dx))
    return wrong==constant(field,field.sub(c,field.mul(a,b)))


def field_oracle(field_name,a,b,c):
    f=FIELDS[field_name]
    cert=conic_bezout(f,a,b,c)
    unit=conic_unit_certificate(f,a,b,c)
    singular=singular_ideal_obstruction(f,a,b,c)
    return {
      "field":field_name,"q":f.q,"a":a,"b":b,"c":c,
      "delta":cert["delta"],
      "identity":cert["identity"],
      "unit_if_nonzero":bool(unit and unit["unit_identity"]),
      "singular_if_zero":singular["all_generators_zero"],
      "unit_certificate":unit,
      "singular_obstruction":singular,
    }
