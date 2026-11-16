"""OLM-19: exact Fraction witnesses for SAE gauge transport and refit aliases.

Pure stdlib; no floating point, neural checkpoint or third-party algebra.
The general written theorems are in OLM19_SAE_GAUGE_AND_REFIT.md.
"""
from fractions import Fraction as Q


def q(x):
    return x if isinstance(x,Q) else Q(x)


def vec(xs):
    return tuple(q(v) for v in xs)


def add(a,b):
    if len(a)!=len(b):raise ValueError("physical dimensions differ")
    return tuple(x+y for x,y in zip(a,b))


def scale(a,s):
    return tuple(x*q(s) for x in a)


def sub(a,b):
    return add(a,scale(b,-1))


def dot(a,b):
    if len(a)!=len(b):raise ValueError("physical dimensions differ")
    return sum((x*y for x,y in zip(a,b)),Q(0))


def norm_squared(a):
    return dot(a,a)


def transpose(A):
    if not A or not A[0] or any(len(row)!=len(A[0]) for row in A):
        raise ValueError("nonempty rectangular matrix expected")
    return tuple(tuple(q(A[i][j]) for i in range(len(A))) for j in range(len(A[0])))


def rowmul(h,M):
    h=vec(h)
    if len(h)!=len(M):
        raise ValueError("row hidden state matrix dimension differs")
    return tuple(dot(h,col) for col in transpose(M))


Q_ROT=((Q(3,5),Q(-4,5)),(Q(4,5),Q(3,5)))


def task_margin(h):
    """A positive, nonlinear bounded-domain task head for the gauge witness."""
    x,y=vec(h)
    return Q(10)+2*x+y+x*y/Q(2)


def recurrent_step(h):
    x,y=vec(h)
    return (x+y*y/Q(3),y-x/Q(5))


def recurrent(h,steps):
    if steps<0:raise ValueError("nonnegative recurrent visits")
    h=vec(h)
    for _ in range(steps):
        h=recurrent_step(h)
    return h


def transported_recurrent(h_rot,steps,Qmatrix=Q_ROT):
    """Q-gauge recurrent T_Q(v)=T(vQ^T)Q."""
    h=vec(h_rot)
    for _ in range(steps):
        h=rowmul(recurrent_step(rowmul(h,transpose(Qmatrix))),Qmatrix)
    return h


def transported_task(h_rot,Qmatrix=Q_ROT):
    return task_margin(rowmul(h_rot,transpose(Qmatrix)))


def orthogonal_transport_witness(steps=3):
    Qm=Q_ROT
    qt=transpose(Qm)
    e1,e2=vec((1,0)),vec((0,1))
    if rowmul(rowmul(e1,Qm),qt)!=e1 or rowmul(rowmul(e2,Qm),qt)!=e2:
        raise AssertionError("rational gauge not orthogonal")
    h=vec((Q(7,5),Q(4,3)))
    edit=vec((Q(2,5),Q(-1,3)))
    base=recurrent(h,steps)
    converted=transported_recurrent(rowmul(h,Qm),steps)
    original_effect=task_margin(recurrent(h,steps))-task_margin(recurrent(sub(h,edit),steps))
    rotated_effect=transported_task(
        transported_recurrent(rowmul(h,Qm),steps))-transported_task(
        transported_recurrent(sub(rowmul(h,Qm),rowmul(edit,Qm)),steps))
    return {
      'steps':steps,
      'original_hidden':h,
      'transported_hidden':rowmul(h,Qm),
      'original_after_recurrence':base,
      'rotated_after_recurrence':converted,
      'source_edit_sq_norm':norm_squared(edit),
      'transported_edit_sq_norm':norm_squared(rowmul(edit,Qm)),
      'original_finite_task_effect':original_effect,
      'transported_finite_task_effect':rotated_effect,
      'finite_effect_identical':original_effect==rotated_effect,
      'hidden_transport_identical':rowmul(base,Qm)==converted
    }


def sae_refit_alias_witness(x=Q(1),y=Q(1)):
    """Two exact-ReLU-reconstructing SAE dictionaries with identical atom two."""
    x,y=q(x),q(y)
    if x<=0 or y<=0:
        raise ValueError("inside the strictly positive ReLU cell only")
    h=vec((x,y))
    a_code=(x,y)
    b_code=(x+y,y)
    da=(vec((1,0)),vec((0,1)))
    db=(vec((1,0)),vec((-1,1)))
    reconstructed_a=add(scale(da[0],a_code[0]),scale(da[1],a_code[1]))
    reconstructed_b=add(scale(db[0],b_code[0]),scale(db[1],b_code[1]))
    if reconstructed_a!=h or reconstructed_b!=h:
        raise AssertionError("SAE exact reconstruction witness failed")
    erased_a=sub(h,scale(da[1],a_code[1]))
    erased_b=sub(h,scale(db[1],b_code[1]))
    m=lambda state:Q(10)+2*state[0]+state[1]
    return {
      'clean_state':h,
      'reference_code':a_code,
      'refit_code':b_code,
      'matched_atom_two_activations_equal':a_code[1]==b_code[1],
      'reference_reconstruction':reconstructed_a,
      'refit_reconstruction':reconstructed_b,
      'reference_decoder_two':da[1],
      'refit_decoder_two':db[1],
      'erased_A':erased_a,
      'erased_B':erased_b,
      'common_clean_margin':m(h),
      'native_erasure_drop_A':m(h)-m(erased_a),
      'native_erasure_drop_B':m(h)-m(erased_b),
    }


def linear_task(h):
    h=vec(h)
    return Q(10)+3*h[0]+4*h[1]


def sharp_physical_stability_bound():
    h=vec((2,1))
    a=vec((0,0))
    b=vec((Q(3,5),Q(4,5)))
    eA=linear_task(h)-linear_task(sub(h,a))
    eB=linear_task(h)-linear_task(sub(h,b))
    norm2=norm_squared(sub(a,b))
    return {'source_drop':eA,
            'target_drop':eB,
            'edit_distance_sq':norm2,
            'absolute_drop_difference':abs(eA-eB),
            'lipschitz_constant':Q(5),
            'squared_stability_ceiling':Q(25)*norm2}


def sign_stability_witness():
    h=vec((2,1));a=vec((1,0));b=vec((1,Q(1,10)))
    eA=linear_task(h)-linear_task(sub(h,a))
    eB=linear_task(h)-linear_task(sub(h,b))
    bound_squared=Q(25)*norm_squared(sub(a,b))
    return {'effect_A':eA,'effect_B':eB,
            'bound_squared':bound_squared,
            'source_sq_effect':eA*eA,
            'same_positive_sign':eA>0 and eB>0}


def equal_dose_angle_witness():
    a=vec((1,0));b=vec((Q(3,5),Q(4,5)))
    squared_dist=norm_squared(sub(a,b))
    cos=dot(a,b)
    return {'dose_squared_A':norm_squared(a),
            'dose_squared_B':norm_squared(b),
            'cosine':cos,'physical_edit_distance_squared':squared_dist,
            'angle_identity_squared':2*(1-cos)}


if __name__=='__main__':
    import json
    def serialize(x):
        if isinstance(x,Q):return str(x)
        if isinstance(x,tuple):return list(map(serialize,x))
        raise TypeError(type(x))
    print(json.dumps({
       'orthogonal_conjugacy':orthogonal_transport_witness(),
       'opposite_native_erasure_alias':sae_refit_alias_witness(),
       'sharp_physical_stability':sharp_physical_stability_bound(),
       'sign_stability':sign_stability_witness(),
       'equal_dose_angle':equal_dose_angle_witness()
    },default=serialize,indent=2))
