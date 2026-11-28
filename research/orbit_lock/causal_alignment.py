"""OLM-14 exact rational witnesses for causal vs activation alignment.

No PyTorch, floating point, neural model files or external dependencies.
The written theorem/proof is OLM14_CROSS_CHECKPOINT_CAUSAL.md.
"""
from fractions import Fraction as Q


def rat(x):
    return x if isinstance(x,Q) else Q(x)


def centered(xs):
    a=tuple(map(rat,xs))
    if len(a)<2:
        raise ValueError("at least two goal tokens required")
    mean=sum(a,Q(0))/len(a)
    return tuple(z-mean for z in a)


def dot(a,b):
    if len(a)!=len(b):
        raise ValueError("response vector dimension mismatch")
    return sum((x*y for x,y in zip(a,b)),Q(0))


def squared_centered_cosine(a,b):
    """Exact magnitude and sign of the puzzle-centered cosine.

    The squared magnitude is rational for rational inputs. Zero-variance
    vectors abstain rather than returning a fabricated zero correlation.
    """
    x,y=centered(a),centered(b)
    if len(x)!=len(y):
        raise ValueError("paired token positions required")
    nx=dot(x,x);ny=dot(y,y)
    if nx<=0 or ny<=0:
        return {'status':'abstain_zero_centered_variance'}
    cov=dot(x,y)
    return {'status':'identified','signed_inner_product':cov,
            'cosine_squared':cov*cov/(nx*ny),
            'sign':0 if cov==0 else (1 if cov>0 else -1)}


def calibration_sign(pairs):
    if not pairs:
        raise ValueError("calibration pairs required")
    total=Q(0)
    for a,b in pairs:
        x,y=centered(a),centered(b)
        if len(x)!=len(y):
            raise ValueError("calibration token count mismatch")
        total+=dot(x,y)
    return 1 if total>=0 else -1


def symmetric_difference(f,h,u,r):
    r=rat(r);h=rat(h);u=rat(u)
    if r<=0 or u==0:
        raise ValueError("nonzero direction and positive radius required")
    return (rat(f(h+r*u))-rat(f(h-r*u)))/(2*r)


def causal_nonidentifiability_witness():
    """Same positive hidden feature and correct label, opposite derivatives."""
    C=Q(3)
    positive_hidden=(Q(1,4),Q(1,2),Q(3,4))
    activations=[x for x in positive_hidden]
    margin_A=[C+x for x in positive_hidden]
    margin_B=[C-x for x in positive_hidden]
    a=symmetric_difference(lambda h:C+h,Q(1,2),1,Q(1,10))
    b=symmetric_difference(lambda h:C-h,Q(1,2),1,Q(1,10))
    assert a==1 and b==-1
    assert min(margin_A)>0 and min(margin_B)>0
    return {'identical_feature_activations':activations,
            'teacher_A_margins':margin_A,
            'teacher_B_margins':margin_B,
            'identical_correct_predictions':True,
            'A_causal_response':a,'B_causal_response':b}


def finite_difference_transfer_witness(radius):
    r=rat(radius)
    if r<=0:
        raise ValueError("positive radius required")
    # For mA(x)=x^3 at h=0, mB(x)=2x^3 at h=0, J=0, and
    # |mA''(x)| <= 6r, |mB''(x)| <= 12r on the segments.
    f=lambda x:x**3
    g=lambda x:2*x**3
    da=symmetric_difference(f,0,1,r)
    db=symmetric_difference(g,0,1,r)
    Ma=6*r;Mb=12*r
    estimated_bound=(Ma+Mb)*r/2
    assert abs(db-da)<=estimated_bound
    return {'finite_response_A':da,'finite_response_B':db,
            'linear_derivative_A':Q(0),'linear_derivative_B':Q(0),
            'curvature_bound_A':Ma,'curvature_bound_B':Mb,
            'transfer_error':abs(db-da),
            'rigorous_transfer_upper':estimated_bound}


def isometric_conjugacy_witness(radius):
    r=rat(radius)
    if r<=0:raise ValueError("positive radius required")
    # P = -1, uA=+1, s=-1, uB=s*P*uA=+1.
    P=-1;s=-1;alpha=Q(3);beta=Q(5)
    mA=lambda x:x*x+2*x
    mB=lambda y:alpha*mA(P*y)+beta
    ha=Q(1,3);hb=P*ha
    ua=Q(1);ub=s*P*ua
    da=symmetric_difference(mA,ha,ua,r)
    db=symmetric_difference(mB,hb,ub,r)
    assert db==s*alpha*da
    return {'source_response':da,'target_response':db,
            'signed_scale':s*alpha,'exact_conjugacy':True}


if __name__=='__main__':
    import json
    def show(v):
        if isinstance(v,Q):return str(v)
        if isinstance(v,tuple):return list(v)
        raise TypeError(type(v))
    print(json.dumps({
        'nonidentifiability':causal_nonidentifiability_witness(),
        'finite_difference':finite_difference_transfer_witness(Q(1,5)),
        'conjugacy':isometric_conjugacy_witness(Q(1,5)),
        'puzzle_centering':squared_centered_cosine((1,2,3),(3,6,9)),
    },default=show,indent=2))
