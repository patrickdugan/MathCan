"""OLM-20 exact rational anchored gradient/refit erasure witnesses.

Dependency-free Fraction arithmetic. These witnesses test explicit sharp
constructions and orthogonal gauge invariance, while the general statements
are proved in OLM20_ANCHORED_GRADIENT_REFIT.md.
"""
from fractions import Fraction as F


def q(x):
    return x if isinstance(x,F) else F(x)


def vec(xs):
    return tuple(q(x) for x in xs)


def dot(x,y):
    if len(x)!=len(y):
        raise ValueError('physical dimension mismatch')
    return sum((a*b for a,b in zip(x,y)), F(0))


def minus(x,y):
    if len(x)!=len(y):
        raise ValueError('physical dimension mismatch')
    return tuple(a-b for a,b in zip(x,y))


def norm2(x):
    return dot(x,x)


def trans(A):
    if not A or any(len(row)!=len(A[0]) for row in A):
        raise ValueError('nonempty matrix rows with consistent width')
    return tuple(tuple(q(row[j]) for row in A) for j in range(len(A[0])))


def rowmat(v,A):
    return tuple(dot(vec(v),column) for column in trans(A))


Q=((F(3,5), F(-4,5)),(F(4,5),F(3,5)))


def finite_erase(m,h,delta):
    return m(h)-m(minus(h,delta))


def anchored_predict(Ea,g,a,b):
    return q(Ea)+dot(g,minus(b,a))


def sharp_quadratic(M=F(4),r=F(3,5)):
    if M<0 or r<=0: raise ValueError('nonnegative Hessian, positive edit length')
    h=vec((0,));a=vec((0,));b=vec((r,))
    m=lambda x:M*x[0]*x[0]/2
    g=vec((0,))
    Ea=finite_erase(m,h,a);Eb=finite_erase(m,h,b)
    pred=anchored_predict(Ea,g,a,b)
    bound=M*(abs(a[0])+abs(b[0]))*abs(b[0]-a[0])/2
    return {'E_ref':Ea,'E_target':Eb,'pred_target':pred,
            'error':abs(Eb-pred),'sharp_bound':bound,
            'source_target_distance_squared':norm2(minus(b,a))}


def linear_dose_witness():
    h=vec((0,0));a=vec((1,0));b=vec((2,0));g=vec((3,0))
    m=lambda x:F(10)+3*x[0]
    Ea=finite_erase(m,h,a);Eb=finite_erase(m,h,b)
    return {'cosine':dot(a,b),'reference_dose_squared':norm2(a),
            'target_dose_squared':norm2(b),'source_effect':Ea,'target_effect':Eb,
            'anchored_predicted_target':anchored_predict(Ea,g,a,b)}


def reversed_sign_witness():
    h=vec((0,));a=vec((0,));b=vec((1,))
    m=lambda x:F(10)+x[0]+2*x[0]*x[0]
    Ea=finite_erase(m,h,a);Eb=finite_erase(m,h,b)
    pred=anchored_predict(Ea,vec((1,)),a,b)
    bound=F(4)*(abs(a[0])+abs(b[0]))*abs(b[0]-a[0])/2
    return {'clean_margin':m(h),'edited_target_margin':m(minus(h,b)),
            'source_effect':Ea,'target_effect':Eb,'predicted_effect':pred,
            'remainder_abs':abs(Eb-pred),'sharp_bound':bound,
            'strict_sign_certificate_holds':abs(pred)>bound}


def orthogonal_witness():
    h=vec((F(1,3),F(5,4)));a=vec((F(3,5),F(1,2)));b=vec((F(4,5),F(-2,3)))
    g=vec((F(2),F(3)))
    m=lambda x:F(10)+2*x[0]+3*x[1]+x[0]*x[1]
    grad=vec((2+h[1],3+h[0]))
    Ea=finite_erase(m,h,a);Eb=finite_erase(m,h,b)
    pred=anchored_predict(Ea,grad,a,b)
    hq=rowmat(h,Q);aq=rowmat(a,Q);bq=rowmat(b,Q);gq=rowmat(grad,Q)
    mq=lambda v:m(rowmat(v,trans(Q)))
    Ea_q=finite_erase(mq,hq,aq);Eb_q=finite_erase(mq,hq,bq)
    predq=anchored_predict(Ea_q,gq,aq,bq)
    return {'source_effect':Ea,'target_effect':Eb,
            'anchored_prediction':pred,
            'transported_source_effect':Ea_q,'transported_target_effect':Eb_q,
            'transported_prediction':predq,
            'original_edit_sq_distance':norm2(minus(b,a)),
            'rotated_edit_sq_distance':norm2(minus(bq,aq)),
            'original_gradient_sq_norm':norm2(grad),
            'rotated_gradient_sq_norm':norm2(gq)}


def equal_dose_norm_witness():
    a=vec((1,0));b=vec((F(3,5),F(4,5)))
    return {'norm_A_sq':norm2(a),'norm_B_sq':norm2(b),
            'edit_distance_sq':norm2(minus(b,a)),
            'angle_dot':dot(a,b)}


if __name__=='__main__':
    import json
    def encode(v):
        if isinstance(v,F): return str(v)
        if isinstance(v,tuple): return list(map(encode,v))
        raise TypeError(type(v))
    print(json.dumps({
        'sharp_quadratic':sharp_quadratic(),
        'linear_dose':linear_dose_witness(),
        'opposite_finite_sign':reversed_sign_witness(),
        'orthogonal_gauge':orthogonal_witness(),
        'equal_dose_example':equal_dose_norm_witness(),
    },indent=2,default=encode))
