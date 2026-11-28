"""DEL-11 exact critical-incidence elimination and bilinear discriminant oracle.

For P(x,y)=sum_i (x_i*y_i + a_i*x_i + b_i*y_i)+c over any
finite field, all gradient entries vanish iff x=-b and y=-a.
At that point the level equation vanishes iff
    c = sum_i a_i*b_i.

This is the explicit affine A^(2n) model. It does not assert
that the same equation characterizes singularity after restricting
the hypersurface to an arbitrary embedded smooth variety U^k.
"""
from itertools import product
from research.deligne_sign_audit.prime_power_fourier import FIELDS


def validate_vector(field, *vectors):
    if not vectors:
        raise ValueError("expected vector")
    n=len(vectors[0])
    if any(len(xs)!=n for xs in vectors):
        raise ValueError("inconsistent vector dimensions")
    if any(x<0 or x>=field.q for xs in vectors for x in xs):
        raise ValueError("field coordinate out of range")
    return n


def field_sum(field, terms):
    result=0
    for item in terms:
        result=field.add(result,item)
    return result


def bilinear_equation(field, a, b, c, x, y):
    n=validate_vector(field,a,b,x,y)
    if not (0<=c<field.q):
        raise ValueError("scalar outside field")
    return field.add(field_sum(field,(
        field.add(field.add(field.mul(x[i],y[i]),
                            field.mul(a[i],x[i])),
                  field.mul(b[i],y[i]))
        for i in range(n))), c)


def bad_discriminant(field, a, b, c):
    validate_vector(field,a,b)
    target=field_sum(field,(field.mul(ai,bi) for ai,bi in zip(a,b)))
    return field.sub(c,target)


def parameter_is_bad(field,a,b,c):
    return bad_discriminant(field,a,b,c)==0


def formal_gradient(field,a,b,x,y):
    n=validate_vector(field,a,b,x,y)
    return (tuple(field.add(y[i],a[i]) for i in range(n)),
            tuple(field.add(x[i],b[i]) for i in range(n)))


def critical_point(field,a,b,c):
    n=validate_vector(field,a,b)
    x=tuple(field.neg(v) for v in b)
    y=tuple(field.neg(v) for v in a)
    gy,gx=formal_gradient(field,a,b,x,y)
    assert not any(gy+gx)
    phase=bilinear_equation(field,a,b,c,x,y)
    assert phase==bad_discriminant(field,a,b,c)
    return x,y,phase


def brute_force_critical_points(field,a,b,c):
    n=validate_vector(field,a,b)
    candidates=[]
    for xs in product(range(field.q),repeat=n):
        for ys in product(range(field.q),repeat=n):
            gy,gx=formal_gradient(field,a,b,xs,ys)
            if any(gy+gx):
                continue
            if bilinear_equation(field,a,b,c,xs,ys)==0:
                candidates.append((xs,ys))
    return tuple(candidates)


def count_bad_parameters(field,n):
    """Exact count using elimination. For each (a,b), exactly one bad c."""
    bad=0
    good=0
    for a in product(range(field.q),repeat=n):
        for b in product(range(field.q),repeat=n):
            s=field_sum(field,(field.mul(a[i],b[i]) for i in range(n)))
            for c in range(field.q):
                if c==s:
                    bad+=1
                else:
                    good+=1
    assert bad==field.q**(2*n)
    assert good==field.q**(2*n)*(field.q-1)
    return good,bad


def constant_one_good_parameter(field,n):
    a=(0,)*n
    b=(0,)*n
    c=1
    return a,b,c,bad_discriminant(field,a,b,c)


def wrong_plus_discriminant(field,a,b,c):
    return field.add(c,field_sum(field,(field.mul(x,y) for x,y in zip(a,b))))


def cross_coupled_discriminant(field,a,b,c):
    if len(a)!=2 or len(b)!=2:
        raise ValueError("cross-coupled mutant requires n=2")
    s=field.add(field.mul(a[0],b[1]),field.mul(a[1],b[0]))
    return field.sub(c,s)


def solve_katz_linear_open(field,n):
    """Lexicographic parameters that also satisfy an illustrative
    Katz principal-open polynomial L=c. This does not construct
    the real Katz good locus for an embedded U^k."""
    for aa in product(range(field.q),repeat=n):
        for bb in product(range(field.q),repeat=n):
            for c in range(field.q):
                if c and bad_discriminant(field,aa,bb,c):
                    return aa,bb,c
    return None
