"""TOE-13: scalar/one-form Ricci-log principal completion of TOE-12.

The original source Bianconi (arxiv:2408.14391) supplies the 0-form
Ricci scalar and 1-form Ricci tensor curvature blocks. We ADD those blocks
on a vacuum homogeneous/isotropic GfE background to the *DECLARED* TOE-11
2-form + Yang--Mills frozen-coefficient trial; they were missing in TOE-12.

This is the algebraically eliminated G-field, log-determinant principal
completion at fixed background. The background and coupled gauge equations
are not recomputed, and none of the lapse/shift, G-field or gauge constraints
have been eliminated. The formal wave derivative convention used by TOE-11
is maintained. This is NOT a proof of a physical gravitational-wave spectrum.
"""
from __future__ import annotations

from fractions import Fraction as F
from .wave_principal import construct_symbol, evaluate_polynomial
from .tensor_subspace import (
    default_params, interpolate_tensor, factored_tensor_at_root,
    field_determinant, _field_evaluate, at_frequency,
)
from .mixed_principal import rat

ETA = (F(-1), F(1), F(1), F(1))


def _check_matrix4(h):
    if len(h) != 4 or any(len(r) != 4 for r in h):
        raise ValueError('symmetric 4x4 metric amplitude required')
    h = tuple(tuple(map(rat, row)) for row in h)
    if any(h[i][j] != h[j][i] for i in range(4) for j in range(4)):
        raise ValueError('nonsymmetric metric perturbation')
    return h


def linearized_ricci(xi, h):
    """Flat-local-frame Ricci principal, with formal derivatives ∂ -> xi.

    δR_mn = (xi_m xi_a h^a_n+xi_n xi_a h^a_m
             -xi_m xi_n h -xi² h_mn)/2.
    No Fourier i factors; use the same formal operator as TOE-11.
    """
    xi = tuple(map(rat, xi))
    if len(xi) != 4:
        raise ValueError('four-component wave covector required')
    h = _check_matrix4(h)
    tr_h = sum((ETA[a]*h[a][a] for a in range(4)), F())
    xi2 = sum((ETA[a]*xi[a]**2 for a in range(4)), F())
    xi_h = tuple(sum((xi[a]*ETA[a]*h[a][nu] for a in range(4)),F()) for nu in range(4))
    ricci = tuple(tuple((xi[mu]*xi_h[nu]+xi[nu]*xi_h[mu]
                          -xi[mu]*xi[nu]*tr_h-xi2*h[mu][nu])/2
                         for nu in range(4)) for mu in range(4))
    scalar = sum((ETA[a]*ricci[a][a] for a in range(4)), F())
    return ricci, scalar


def metric_tensor_mode(cross=False):
    h = [[F() for _ in range(4)] for _ in range(4)]
    if cross:
        h[1][2] = h[2][1] = F(1)
    else:
        h[1][1],h[2][2] = F(1),F(-1)
    return tuple(tuple(x) for x in h)


def background_denominators(A, Bcurv, beta, time_matter=0):
    """0/1-form curvature eigenvalues, plus a declared temporal matter shift.

    theta0=1-6 beta(A+B), theta_t=1-3 beta A+time_matter,
    theta_s=1-beta(A+2 B). A temporal scalar gradient enters theta_t
    and leaves the TT spatial Ricci principal invariant at fixed matter.
    """
    A,Bcurv,beta,time_matter = map(rat,(A,Bcurv,beta,time_matter))
    if beta <= 0:
        raise ValueError('positive beta required')
    values=(1-6*beta*(A+Bcurv),1-3*beta*A+time_matter,
            1-beta*(A+2*Bcurv))
    if min(values)<=0:
        raise ValueError('positive G-field 0/1-form denominators required')
    return values


def form_sector_bilinear(xi, h, k, *, A, Bcurv, beta, sigma0, sigma1,
                          time_matter=0):
    """Exact principal quadratic form of -sigma0 log theta0 -sigma1 log det Theta1.

    Full mixed 4x4 Ricci operator: Theta1=I-beta*Ricci^(mu)_nu at
    the frozen FLRW background. Second variation of the logarithms is
    beta² times the inverse-operator bilinear; δ² Ricci terms are only
    second-order in h and omitted from this fourth-order principal.
    """
    s0,s1,beta=map(rat,(sigma0,sigma1,beta))
    if min(s0,s1)<0:raise ValueError('nonnegative form coefficients required')
    th0,tht,ths=background_denominators(A,Bcurv,beta,time_matter)
    hR,hs=linearized_ricci(xi,h)
    kR,ks=linearized_ricci(xi,k)
    inv=(1/tht,1/ths,1/ths,1/ths)
    # h Ric^mu_nu = eta^mu,mu hR_mu,nu. Trace J dR J dR.
    vector=sum((inv[i]*inv[j]*ETA[i]*ETA[j]*hR[i][j]*kR[j][i]
                for i in range(4) for j in range(4)), F())
    scalar=s0*beta*beta*hs*ks/(th0*th0)
    vector=s1*beta*beta*vector
    return {'scalar':scalar,'vector':vector,'total':scalar+vector,
            'theta0':th0,'theta_t':tht,'theta_s':ths,
            'delta_scalar_h':hs,'delta_scalar_k':ks}


def tt_vector_coefficient(*,A,Bcurv,beta,sigma1):
    _,_,ts=background_denominators(A,Bcurv,beta)
    return rat(sigma1)*rat(beta)**2/(2*ts**2)


def tt_form_matrix(omega, *, A,Bcurv,beta,sigma0=0,sigma1=0,time_matter=0):
    xi=(rat(omega),0,0,1)
    hs=(metric_tensor_mode(False),metric_tensor_mode(True))
    return tuple(tuple(form_sector_bilinear(xi,h,k,A=A,Bcurv=Bcurv,beta=beta,
              sigma0=sigma0,sigma1=sigma1,time_matter=time_matter)['total']
              for k in hs) for h in hs)


def augmented_six_mode(omega, *, sigma0=0, sigma1=0, time_matter=0, **params):
    from .tensor_subspace import bilinear_matrix
    original=bilinear_matrix(omega,**params)
    correction=tt_form_matrix(omega,A=params['A'],Bcurv=params['Bcurv'],
                   beta=params['beta'],sigma0=sigma0,sigma1=sigma1,
                   time_matter=time_matter)
    return tuple(tuple(original[i][j]+(correction[i][j] if i<2 and j<2 else 0)
                  for j in range(6)) for i in range(6))


def augmented_coefficients(*,sigma0=0,sigma1=0,**params):
    coeff=dict(interpolate_tensor(**params))
    k=tt_vector_coefficient(A=params['A'],Bcurv=params['Bcurv'],
                             beta=params['beta'],sigma1=sigma1)
    for i in (0,1):
        baseline=coeff[(i,i)]
        coeff[(i,i)]=tuple(v+u for v,u in zip(baseline,(k,0,-2*k,0,k)))
    return coeff


def lift_old_root(*,sigma1=F(1,100),**params):
    """Exact six-mode determinant at former repeated root, over Q(sqrt(r)).

    Original metric/mixed blocks vanish at r. With 1-form Ricci, the
    two TT diagonal entries become k*(r-1)^2. Thus the determinant is
    [k*(r-1)^2]^2 times the original gauge determinant G(r).
    """
    if sigma1<=0:raise ValueError('nonzero vector-sector response required')
    p=construct_symbol(**params)
    r=p.doubled_gravity_root
    orig=interpolate_tensor(**params)
    fact=factored_tensor_at_root(orig,r)
    k=tt_vector_coefficient(A=params['A'],Bcurv=params['Bcurv'],
                             beta=params['beta'],sigma1=sigma1)
    coeff=augmented_coefficients(sigma1=sigma1,**params)
    m=tuple(tuple(_field_evaluate(coeff[(i,j)] if i<=j else coeff[(j,i)],r)
                  for j in range(6)) for i in range(6))
    determinant,rank=field_determinant(m,r)
    gd=fact['gauge_determinant']
    expected=(k*k*(r-1)**4*gd[0],k*k*(r-1)**4*gd[1])
    if r==1 or not any(gd) or rank!=6 or determinant!=expected or not any(determinant):
        raise AssertionError('the 1-form curvature response must lift the old root')
    return {'old_squared_frequency':r,'vector_coefficient':k,
            'root_determinant':determinant,'expected':expected,
            'root_rank':rank,'old_root_lifted':True,
            '0form_TT_fourth_order':F(0)}


def cubic_discriminant(coeffs):
    """Exact discriminant of a*x^3+b*x^2+c*x+d, ascending coefficients."""
    if len(coeffs)!=4:raise ValueError('cubic coefficient list required')
    d,c,b,a=map(rat,coeffs)
    if a==0:raise ValueError('noncubic polynomial')
    return 18*a*b*c*d-4*b**3*d+b*b*c*c-4*a*c**3-27*a*a*d*d


def restricted_with_vector(*,sigma1=F(1,100),**params):
    """Exact formal two-mode cubic, plus the discriminant and signs.

    Note the TOE-11 odd-derivative/Fourier phase convention: this is a
    formal polynomial diagnostic, not a verified dispersion relation.
    """
    p=construct_symbol(**params)
    k=tt_vector_coefficient(A=params['A'],Bcurv=params['Bcurv'],
                             beta=params['beta'],sigma1=sigma1)
    g0,g1=p.ff
    a0,a1,a2,a3=p.determinant
    coeff=(a0+k*g0,a1+k*(g1-2*g0),a2+k*(g0-2*g1),a3+k*g1)
    disc=cubic_discriminant(coeff)
    r=p.doubled_gravity_root
    if evaluate_polynomial(coeff,r)!=k*(r-1)**2*(g0+g1*r):
        raise AssertionError('old root lift inconsistent')
    return {'coefficients':coeff,'discriminant':disc,
            'one_real_two_complex_x':disc<0,
            'one_positive_real_x':disc<0 and evaluate_polynomial(coeff,0)<0 and evaluate_polynomial(coeff,1)>0,
            'old_root':r,'value_at_old_root':evaluate_polynomial(coeff,r)}


def reference_experiment():
    kw=default_params()
    v=lift_old_root(sigma1=F(1,100),**kw)
    c=restricted_with_vector(sigma1=F(1,100),**kw)
    return {'schema':'mathcan.toe13.formsector.v1',
            'scope':'conditional 0/1-form TT fourth-order completion of declared 2-form/YM model',
            'parameters':{k:([str(a) for a in x] if isinstance(x,tuple) else str(x)) for k,x in kw.items()},
            'sigma0':'1/100','sigma1':'1/100',
            'old_root_r':str(v['old_squared_frequency']),
            'vector_TT_quartic_coeff':str(v['vector_coefficient']),
            'root_det_nonzero':v['old_root_lifted'],
            'root_det_sign':1 if v['root_determinant'][0]>0 else -1,
            'formal_two_mode_cubic_discriminant_sign': 1 if c['discriminant']>0 else -1,
            'formal_two_mode_one_real_two_complex_x':c['one_real_two_complex_x'],
            'full_GfE_constraints_derived':False,
            'full_theory_strong_hyperbolicity_verified':False}

if __name__=='__main__':
    import json
    print(json.dumps(reference_experiment(),indent=2,sort_keys=True))
