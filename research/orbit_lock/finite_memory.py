"""OLM-03: exact-rational finite-memory frontier for a uniform orbit label.

A channel X->Z is row-stochastic; p(X) is uniform. Every TV and recovery
probability is computed using Fraction. Trigonometric diagnostics are
floating-point and accompanied by a separate analytic robustness bound.
"""
from fractions import Fraction
from itertools import product
from math import factorial, cos, sin, pi

ZERO=Fraction(0)
ONE=Fraction(1)

def tv(a,b):
    return sum((abs(a.get(k,ZERO)-b.get(k,ZERO)) for k in a.keys() | b.keys()),ZERO)/2

def channel_certificate(rows):
    """Rows x -> probabilities z with uniform p(x); output support may shrink."""
    if not rows:
        raise ValueError('at least one state required')
    m=len(rows)
    zset=set().union(*(row.keys() for row in rows))
    if not zset:
        raise ValueError('channel outputs must be nonempty')
    if any(sum(row.values(),ZERO)!=ONE or any(p<0 for p in row.values()) for row in rows):
        raise ValueError('invalid probability channel')
    q={z:sum((row.get(z,ZERO) for row in rows),ZERO)/m for z in zset}
    joint={(x,z):rows[x].get(z,ZERO)/m for x in range(m) for z in zset}
    independent={(x,z):q[z]/m for x in range(m) for z in zset}
    d=tv(joint,independent)
    best=sum((max(joint[x,z] for x in range(m)) for z in zset),ZERO)
    r=len([z for z in zset if q[z]>0])
    assert d<=ONE-max(Fraction(1,m),Fraction(1,r))
    assert best<=min(ONE,Fraction(r,m))
    return {'m':m,'r_used':r,'tv':d,'best_recovery':best,
            'output_collision':sum((v*v for v in q.values()),ZERO),
            'joint':joint,'independent':independent}

def balanced_partition(m,r):
    if m<1 or not (1<=r<=m):
        raise ValueError('require 1<=r<=m')
    return tuple(i%r for i in range(m))

def deterministic_certificate(encoding):
    return channel_certificate([{z:ONE} for z in encoding])

def frontier(m,r):
    enc=balanced_partition(m,r)
    c=deterministic_certificate(enc)
    q,s=divmod(m,r)
    collision=Fraction((r-s)*q*q+s*(q+1)*(q+1),m*m)
    assert c['output_collision']==collision
    assert c['tv']==ONE-collision
    assert c['best_recovery']==Fraction(r,m)
    return {'m':m,'r':r,'sizes':tuple(sorted(enc.count(z) for z in range(r))),
            'tv':c['tv'],'recovery':c['best_recovery'],
            'balanced_accuracy':(ONE+c['tv'])/2,
            'memory_bits_ceil':(r-1).bit_length()}

def exhaustive_frontier(m,r):
    if m>6 or r**m>30000:
        raise ValueError('bounded exhaustive test only')
    optimum=ZERO
    maximizers=0
    for enc in product(range(r),repeat=m):
        gap=deterministic_certificate(enc)['tv']
        if gap>optimum:
            optimum=gap;maximizers=1
        elif gap==optimum:
            maximizers+=1
    assert optimum==frontier(m,r)['tv']
    return (optimum,maximizers)

def stabilizer_quotient(k):
    if k<1:
        raise ValueError('k>=1')
    numerator=factorial(2*k)
    stabilizer=(2**k)*factorial(k)
    quotient=numerator//stabilizer
    assert numerator==stabilizer*quotient
    return {'vertices':2*k,'group_order':numerator,'stabilizer_order':stabilizer,
            'matching_states':quotient,'minimum_exact_bits':(quotient-1).bit_length(),
            'full_group_bits':(numerator-1).bit_length()}

def circle_probe(m,b):
    """Numerical code diagnostic; analytic sufficient bound checked separately."""
    if m<3 or b<0:
        raise ValueError('m>=3,b>=0 required')
    c=cos(2*pi/m)
    threshold=(1+c)/2
    scale=2**b
    codes=[(round(scale*cos(2*pi*j/m))/scale,
            round(scale*sin(2*pi*j/m))/scale) for j in range(m)]
    minsame=min(sum(t*t for t in u) for u in codes)
    maxdifferent=max(sum(a*b for a,b in zip(codes[i],codes[j]))
                     for i in range(m) for j in range(m) if i!=j)
    delta=2**(-b-1)
    perturb_upper=4*delta+2*delta*delta
    margin=(1-c)/2
    return {'m':m,'b':b,'distinct_codes':len(set(codes)),
            'threshold':threshold,'same_min':minsame,'different_max':maxdifferent,
            'empirical_separated':minsame>threshold>maxdifferent,
            'sufficient_analytic_bound':perturb_upper<margin,
            'perturb_upper':perturb_upper,'margin':margin,
            'memory_bits_2d_integer_storage':2*(b+2)}

if __name__=='__main__':
    import json
    print(json.dumps({
        'frontier_15':[{k:str(v) if isinstance(v,Fraction) else v
                        for k,v in frontier(15,r).items()} for r in (1,2,3,4,5,8,15)],
        'stabilizer':[stabilizer_quotient(k) for k in range(2,6)],
        'circle_15':[circle_probe(15,b) for b in range(2,9)]
    },indent=2))
