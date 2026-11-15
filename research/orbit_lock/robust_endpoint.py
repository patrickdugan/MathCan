"""OLM-10 exact-rational outer boxes for robust finite endpoint comparisons.

A direction u is an exact-real unit vector. Every admissible alternative
unit direction u' has ||u'-u||_2 <= du, and the selected 48-channel token
anchor moves by at most dh in L2. Coordinate boxes enclose those L2 balls.
"""
from fractions import Fraction as Q


def rat(v):
    return v if isinstance(v, Q) else Q(v)


def centered_interval(value, radius):
    v, r = rat(value), rat(radius)
    if r < 0:
        raise ValueError('negative radius')
    return v-r, v+r


def input_boxes(center, active, control, shift_radius, anchor_uncertainty,
                active_uncertainty, control_uncertainty):
    """Componentwise boxes enclosing every admitted Euclidean perturbation.

    All vectors have equal length. Requires normalizations to be enforced by
    the caller; the inclusions remain sound for any vectors regardless.
    """
    n=len(center)
    if n==0 or len(active)!=n or len(control)!=n:
        raise ValueError('inconsistent or empty vector lengths')
    r,da,du,dv=map(rat,(shift_radius,anchor_uncertainty,
                         active_uncertainty,control_uncertainty))
    if r<=0 or min(da,du,dv)<0:
        raise ValueError('radius > 0, uncertainty >= 0 required')
    h=tuple(map(rat,center));u=tuple(map(rat,active));v=tuple(map(rat,control))
    return {
      'clean':tuple(centered_interval(z,da) for z in h),
      'active':tuple(centered_interval(h[i]+r*u[i],da+r*du) for i in range(n)),
      'control':tuple(centered_interval(h[i]+r*v[i],da+r*dv) for i in range(n)),
      'r':r,
      'anchor_uncertainty':da,
      'active_direction_uncertainty':du,
      'control_direction_uncertainty':dv,
    }


def overlap_region(outer,inner):
    """Verify a one-dimensional interval includes another interval."""
    return outer[0]<=inner[0] and inner[1]<=outer[1]


def contains_all_boxes(outer,inner):
    return all(all(overlap_region(a,b) for a,b in zip(outer[k],inner[k]))
               for k in ('clean','active','control'))


def raw_to_unit_direction_error(relative_raw_error):
    """Upper bound for ||normalized(w+e)-normalized(w)||_2.

    If ||e||_2 <= q ||w||_2 and 0<=q<1, then <= 2q/(1-q).
    The result may exceed 2; that is a valid but vacuous upper bound.
    """
    q=rat(relative_raw_error)
    if not 0<=q<1:
        raise ValueError('relative raw weight error must be in [0,1)')
    return 2*q/(1-q)


def add(a,b):
    return a[0]+b[0],a[1]+b[1]


def mul(a,b):
    p=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
    return min(p),max(p)


def subtract(a,b):
    return a[0]-b[1],a[1]-b[0]


def square(a):
    hi=max(a[0]**2,a[1]**2)
    return (Q(0) if a[0]<=0<=a[1] else min(a[0]**2,a[1]**2),hi)


def linear_forward(box,matrix):
    """Interval inclusion for a specified exact-rational linear network."""
    n=len(box)
    if not matrix or any(len(row)!=n for row in matrix):
        raise ValueError('wrong linear-map shape')
    return tuple(sum_intervals(tuple(mul((rat(k),rat(k)),iv)
                                    for k,iv in zip(row,box))) for row in matrix)


def sum_intervals(items):
    s=(Q(0),Q(0))
    for x in items:
        s=add(s,x)
    return s


def squared_effect(logits,clean):
    if len(logits)!=len(clean) or not logits:
        raise ValueError('output shapes mismatch')
    return sum_intervals(tuple(square(subtract(a,b)) for a,b in zip(logits,clean)))


def robust_linear_comparison(center,active,control,radius,da,du,dv,matrix):
    box=input_boxes(center,active,control,radius,da,du,dv)
    clean=linear_forward(box['clean'],matrix)
    A=squared_effect(linear_forward(box['active'],matrix),clean)
    B=squared_effect(linear_forward(box['control'],matrix),clean)
    return {'active_squared':A,'control_squared':B,
            'status':'active_greater' if A[0]>B[1] else
                'control_greater' if B[0]>A[1] else 'inconclusive'}


def containment_witness(center,active,control,r,da,du,dv,actual_h,actual_u,actual_v):
    """Exact rational check of input enclosures for supplied admissible values.

    Euclidean checks are done on *squared* norms, without sqrt roundoff.
    """
    box=input_boxes(center,active,control,r,da,du,dv)
    def squared_distance(a,b):
        return sum(((rat(x)-rat(y))**2 for x,y in zip(a,b)),Q(0))
    if not (squared_distance(actual_h,center)<=rat(da)**2 and
            squared_distance(actual_u,active)<=rat(du)**2 and
            squared_distance(actual_v,control)<=rat(dv)**2):
        raise ValueError('witness exceeds its declared Euclidean uncertainty')
    for label,shift in (('clean',None),('active',actual_u),('control',actual_v)):
        vals=[rat(h)+rat(r)*(rat(shift[i]) if shift is not None else Q(0))
              for i,h in enumerate(actual_h)]
        if not all(lo<=v<=hi for v,(lo,hi) in zip(vals,box[label])):
            raise AssertionError('geometric containment violated')
    return True




def lipschitz_effect_enclosure(nominal_effect, clean_lipschitz,
                               endpoint_lipschitz, radius,
                               anchor_uncertainty,direction_uncertainty):
    """Exact endpoint effect bounds from two independently certified local L.

    nominal_effect=(known lower,known upper) for ||F(h+r*u)-F(h)||.
    L0 valid on radius dh ball about h, L1 valid on radius dh+r*du
    about h+r*u. Both perturbed and clean have common unknown anchor.
    """
    lo,hi=map(rat,nominal_effect)
    L0,L1,r,da,du=map(rat,(clean_lipschitz,endpoint_lipschitz,radius,
                            anchor_uncertainty,direction_uncertainty))
    if min(lo,L0,L1,da,du)<0 or hi<lo or r<=0:
        raise ValueError('invalid norm, Lipschitz or uncertainty values')
    eps=L0*da+L1*(da+r*du)
    return (max(Q(0),lo-eps),hi+eps)


def lipschitz_ordering(active_effect,control_effect,
                       clean_lipschitz,active_endpoint_lipschitz,
                       control_endpoint_lipschitz,r,da,du,dv):
    """Uniform effect ordering over every admitted Euclidean neighborhood."""
    A=lipschitz_effect_enclosure(active_effect,clean_lipschitz,
                                 active_endpoint_lipschitz,r,da,du)
    B=lipschitz_effect_enclosure(control_effect,clean_lipschitz,
                                 control_endpoint_lipschitz,r,da,dv)
    return {'active_effect_interval':A,'control_effect_interval':B,
            'status':'active_greater' if A[0]>B[1] else
               'control_greater' if B[0]>A[1] else 'inconclusive'}

if __name__ == '__main__':
    import json
    W=((Q(2),Q(0)),(Q(0),Q(1)))
    out=robust_linear_comparison((0,0),(1,0),(0,1),Q(1,5),
                                 Q(1,100),Q(1,100),Q(1,100),W)
    print(json.dumps({k:([str(x) for x in v] if isinstance(v,tuple) else v)
                      for k,v in out.items()},indent=2))
