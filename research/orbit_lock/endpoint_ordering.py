"""OLM-09: exact rational endpoint interval and robustness certificates.

This oracle is independent of Arb and of the pretrained TRM. Its job is
to verify the mathematics of an interval separating squared output norms.
The applied SMC-09 engine uses validated Arb recurrence interval endpoints.
"""
from fractions import Fraction as Q
from math import isqrt


def fraction(x):
    return x if isinstance(x,Q) else Q(x)


def interval(lo,hi):
    lo,hi=fraction(lo),fraction(hi)
    if lo>hi:raise ValueError('reversed interval bounds')
    return (lo,hi)


def subtract(a,b):
    return (a[0]-b[1],a[1]-b[0])


def square(a):
    lo,hi=a
    bound=max(lo*lo,hi*hi)
    if lo<=0<=hi:
        return (Q(0),bound)
    return (min(lo*lo,hi*hi),bound)


def add(a,b):
    return a[0]+b[0],a[1]+b[1]


def squared_effect(logits,baseline):
    if not logits or len(logits)!=len(baseline):
        raise ValueError('nonempty same-size output vectors required')
    result=(Q(0),Q(0))
    for x,y in zip(logits,baseline):
        result=add(result,square(subtract(x,y)))
    return result


def ordering(active,control):
    """Return strict result only when every included real pair obeys it."""
    if active[0]>control[1]:
        return 'active_greater'
    if active[1]<control[0]:
        return 'control_greater'
    return 'inconclusive'


def sqrt_lower(x,bits=32):
    """Dyadic lower sqrt for a nonnegative rational, via integer arithmetic."""
    x=fraction(x)
    if x<0 or bits<1:
        raise ValueError('nonnegative value and bits>=1 required')
    scale=1<<(bits*2)
    integer=isqrt((x.numerator*scale)//x.denominator)
    lo=Q(integer,1<<bits)
    assert lo*lo<=x
    return lo


def sqrt_upper(x,bits=32):
    x=fraction(x)
    lo=sqrt_lower(x,bits)
    if lo*lo==x:
        return lo
    upper=lo+Q(1,1<<bits)
    assert upper*upper>=x
    return upper


def robust_ordering(active,control,lip,radius,anchor_uncertainty,
                    active_direction_uncertainty,control_direction_uncertainty,
                    bits=48):
    """Conservative sufficient condition for uncertainty-uniform ranking."""
    l,r=map(fraction,(lip,radius))
    h,da,db=map(fraction,(anchor_uncertainty,active_direction_uncertainty,
                         control_direction_uncertainty))
    if min(l,r,h,da,db)<0:
        raise ValueError('all parameters nonnegative')
    if active[0]<0 or control[1]<0:
        raise ValueError('squared effects must be nonnegative')
    lower=sqrt_lower(active[0],bits)
    upper=sqrt_upper(control[1],bits)
    budget=l*(r*(da+db)+4*h)
    return {'certified':lower-upper>budget,'lower_effect_gap':lower-upper,
            'uncertainty_budget':budget}


def example():
    clean=((Q(0),Q(0)),(Q(0),Q(0)))
    active=((Q(19,10),Q(21,10)),(Q(0),Q(0)))
    control=((Q(9,10),Q(11,10)),(Q(0),Q(0)))
    A=squared_effect(active,clean)
    B=squared_effect(control,clean)
    return {'active_squared_interval':tuple(map(str,A)),
            'control_squared_interval':tuple(map(str,B)),
            'dominance':ordering(A,B),
            'small_uncertainty_certified':robust_ordering(A,B,1,Q(1,5),
                                                         Q(1,100),
                                                         Q(1,100),
                                                         Q(1,100))['certified']}


if __name__=="__main__":
    import json
    print(json.dumps(example(),indent=2))
