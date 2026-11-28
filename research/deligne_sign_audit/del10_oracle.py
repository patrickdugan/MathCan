"""DEL-10: exact finite-field nonvanishing witnesses for principal opens.

Proof boundary:
Mathlib's multivariate Nullstellensatz certifies existence over every
finite field with per-variable degrees strictly below its cardinality.
This oracle enumerates finite cases, adversarial degree-bound failures
and extension-field repairs. It does not construct Bertini/Katz opens.
"""
from itertools import product
from research.deligne_sign_audit.prime_power_fourier import FIELDS


def canonical_polynomial(field, terms, n):
    """Sparse polynomial as [(coefficient, [exponents...]), ...].
    Combine equal monomials formally; coefficients are field elements."""
    coeff={}
    for c, powers in terms:
        power=tuple(powers)
        if len(power)!=n or any(int(e)!=e or e<0 for e in power):
            raise ValueError("invalid nonnegative multidegree")
        if c<0 or c>=field.q:
            raise ValueError("coefficient outside field")
        coeff[power]=field.add(coeff.get(power,0),int(c))
    return {k:v for k,v in coeff.items() if v!=0}


def degree_vector(poly,n):
    if not poly:
        return (0,)*n
    return tuple(max(exp[i] for exp in poly) for i in range(n))


def evaluate(field,poly,point):
    x=0
    for exps,coeff in poly.items():
        t=coeff
        for y,e in zip(point,exps):
            t=field.mul(t,field.pow(y,e))
        x=field.add(x,t)
    return x


def find_common_witness(field,polys,n):
    """Lexicographic first point at which all polynomials are nonzero."""
    for point in product(range(field.q),repeat=n):
        if all(evaluate(field,p,point)!=0 for p in polys):
            return point
    return None


def degree_budget(field,polys,n):
    return tuple(sum(degree_vector(p,n)[j] for p in polys)
                 for j in range(n))


def exact_case(field_name,terms,n):
    field=FIELDS[field_name]
    polys=[canonical_polynomial(field,t,n) for t in terms]
    degrees=degree_budget(field,polys,n)
    witness=find_common_witness(field,polys,n)
    return {
      "field":field_name,"q":field.q,"n":n,
      "nonzero_polynomials":all(p for p in polys),
      "degrees":degrees,"strict_degree_gate":all(d<field.q for d in degrees),
      "exists":witness is not None,
      "witness":witness,
      "polynomials":polys,
    }


def linear_term(field,a,coordinate,n,sign=-1):
    """The polynomial x_coordinate - a; sign is -1 by default."""
    if coordinate>=n:
        raise ValueError("bad coordinate index")
    exp=tuple(int(i==coordinate) for i in range(n))
    zero=(0,)*n
    return [(field.neg(a),list(zero)),(1,list(exp))]


def constant(field,c,n):
    return [(c,[0]*n)]


def frobenius_gap_terms(field,n=1):
    """X^p-X, nonzero formal polynomial that vanishes on F_p."""
    high=(field.p,)+(0,)*(n-1)
    low=(1,)+(0,)*(n-1)
    return [(1,list(high)),(field.neg(1),list(low))]


def high_degree_nonzero_terms(field,n=1):
    """X^q+1 has degree q and is nonzero at x=0.
    Shows the strict degree condition is sufficient, not necessary."""
    high=(field.q,)+(0,)*(n-1)
    return [(1,list(high)),(1,[0]*n)]


def chart_linear_terms(field,n=2):
    return linear_term(field,0,n-1,n)
