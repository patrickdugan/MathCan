"""OLM-16 rational projection, tangent and curvature witnesses.

Exact arithmetic only, with no numerical linear algebra dependency.
"""
from fractions import Fraction as Q


def q(x):
    return x if isinstance(x,Q) else Q(x)


def vector(values):
    return tuple(q(x) for x in values)


def dot(a,b):
    if len(a)!=len(b):
        raise ValueError('vector dimension mismatch')
    return sum((x*y for x,y in zip(a,b)),Q(0))


def add(a,b):
    if len(a)!=len(b):
        raise ValueError('vector dimension mismatch')
    return tuple(x+y for x,y in zip(a,b))


def scale(v,c):
    return tuple(q(c)*x for x in v)


def negate(v):
    return scale(v,-1)


def norm_squared(v):
    return dot(v,v)


def orthogonal_rows(rows):
    """Fraction-only Gram-Schmidt with explicit rank defect refusal."""
    basis=[]
    for row in rows:
        v=vector(row)
        if basis and len(v)!=len(basis[0]):
            raise ValueError('row width differs')
        for b in basis:
            v=add(v,scale(b,-dot(v,b)/norm_squared(b)))
        if norm_squared(v)==0:
            raise ValueError('preserved rows linearly dependent')
        basis.append(v)
    return basis


def project_off_rows(a,rows):
    a=vector(a)
    if not a:
        raise ValueError('empty vector')
    basis=orthogonal_rows(rows)
    if any(len(row)!=len(a) for row in basis):
        raise ValueError('physical dimension differs')
    v=a
    for row in basis:
        v=add(v,scale(row,-dot(a,row)/norm_squared(row)))
    return v


def minimum_selective_edit(selected,others,coefficient,overshoot):
    a=vector(selected)
    z,tau=q(coefficient),q(overshoot)
    if z<=0 or tau<=0:
        raise ValueError('positive selected activation and overshoot required')
    v=project_off_rows(a,others)
    denom=norm_squared(v)
    if denom==0:
        raise ValueError('selected row lies in preserved row span')
    edit=scale(v,(z+tau)/denom)
    if dot(a,edit)!=z+tau or any(dot(vector(row),edit)!=0 for row in others):
        raise ArithmeticError('exact projection constraints failed')
    return edit


def tangent_sham(active_rows,seed_vector,target_norm_squared):
    target=q(target_norm_squared)
    if target<=0:
        raise ValueError('positive dose required')
    v=project_off_rows(seed_vector,active_rows)
    n=norm_squared(v)
    if n==0:
        raise ValueError('seed vector has no tangent component')
    # Rational scale exists whenever target/n has a rational square root.
    from math import isqrt
    ratio=target/n
    nu=isqrt(ratio.numerator);de=isqrt(ratio.denominator)
    if nu*nu!=ratio.numerator or de*de!=ratio.denominator:
        raise ValueError('requested norm lacks rational scaling')
    out=scale(v,Q(nu,de))
    assert norm_squared(out)==target
    assert all(dot(vector(row),out)==0 for row in active_rows)
    return out


def native_margin_drop(f,h,delta):
    h=vector(h);delta=vector(delta)
    return f(h)-f(add(h,negate(delta)))


def sharp_quadratic_witness(radius=Q(3,5),curvature=Q(4)):
    r,M=q(radius),q(curvature)
    if r<=0 or M<0:
        raise ValueError('positive radius, nonnegative curvature')
    h=vector((0,0,0))
    kill=vector((r,0,0));sham=vector((0,0,r))
    m=lambda x: M*(x[0]**2-x[2]**2)/2
    measured=native_margin_drop(m,h,kill)-native_margin_drop(m,h,sham)
    bound=M*r*r
    assert abs(measured)==bound
    return {'observed_difference':measured,
            'zero_clean_derivative':True,'curvature_bound':bound}


def inactive_task_counterexample():
    h=vector((1,1,1))
    kill=minimum_selective_edit((1,0,0),[(0,1,0)],1,Q(1,5))
    sham=tangent_sham([(1,0,0),(0,1,0)],(0,0,1),
                      norm_squared(kill))
    margin=lambda x:Q(10)+x[1]
    effect=native_margin_drop(margin,h,kill)-native_margin_drop(margin,h,sham)
    return {'clean_selected_activation':Q(1),
            'selective_edit':kill,
            'tangent_sham':sham,
            'task_effect_difference':effect}


if __name__=='__main__':
    import json
    def serialize(v):
        if isinstance(v,Q):return str(v)
        if isinstance(v,tuple):return list(map(str,v))
        raise TypeError(type(v))
    print(json.dumps({
      '3d_example':{
       'selective_edit':minimum_selective_edit(
           (1,2,0),[(0,1,0)],Q(3,2),Q(1,5)),
       'unit_tangent':tangent_sham([(1,0,0),(0,1,0)],(0,0,1),Q(1))
      },
      'sharp_curvature':sharp_quadratic_witness(),
      'active_but_unnecessary':inactive_task_counterexample()
    },default=serialize,indent=2))
