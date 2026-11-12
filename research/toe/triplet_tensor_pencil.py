"""TOE-17: exact source-derived frequency-dependent tensor-multiplet pencil.

A foundational three-multiplet Dirac--Kahler local-jet configuration has
(D Phi_i)_(2)=e_(B_i), (Phi_i)_(2)=e_(B_i), lambda=m²+xi*R=1 at an event,
with 0/1-form background matter blocks zero. On an FLRW frozen curvature
with A=2/5, B=1, alpha=3/500, beta=1/100, its E/B response matches.

The 4th/3rd/2nd derivative metric--one-form pencil is derived directly
from the source -Tr_F log Theta, including the 1-form Ricci metric term
and full 6x6 E/B bivector trace. Neither a bare Yang--Mills term nor
the TOE-11 synthetic sigma is used. Its spin-two transverse one-form
variations have zero scalar coderivative and no first-order D Phi_(1).
Metric-dependent Hodge-adjoint / potential / background terms of lower
weighted differential order and all non-spin2 fields are out of scope.

This remains a frozen, off-shell, restricted Douglis--Nirenberg principal
subsystem. Its formal Jordan result does not establish hyperbolicity of
the physical constrained GfE Cauchy evolution.
"""
from __future__ import annotations
from fractions import Fraction as F

from .mixed_principal import det,rat
from .operator_principal import (
    S, gram_first, gram_second, mul, trace, wave_riemann_pair,
    wave_field_strength
)
from .form_sector_principal import linearized_ricci,metric_tensor_mode,ETA
from .form_sector_principal import background_denominators
from .form_sector_principal import cubic_discriminant
from .wave_principal import evaluate_polynomial


DEFAULT_ALPHA=F(3,500)
DEFAULT_BETA=F(1,100)
DEFAULT_A=F(2,5)
DEFAULT_B=F(1)
DEFAULT_LAMBDA=F(1)
PAIRS=((0,1),(0,2),(0,3),(2,3),(3,1),(1,2))


def source_responses(*,alpha=DEFAULT_ALPHA,beta=DEFAULT_BETA,
                     A=DEFAULT_A,B=DEFAULT_B,lam=DEFAULT_LAMBDA):
    """Positive source denominators for local triplet, with mE=0, mB=1+lam."""
    alpha,beta,A,B,lam=map(rat,(alpha,beta,A,B,lam))
    if alpha<=0 or beta<=0 or lam<=0:
        raise ValueError('positive alpha,beta,lambda required')
    theta0,theta_t,theta_s=background_denominators(A,B,beta)
    theta_e=1-2*beta*A
    theta_b=1+alpha*(1+lam)-2*beta*B
    if min(theta_e,theta_b)<=0:
        raise ValueError('positive bivector response required')
    return {'theta0':theta0,'theta_t':theta_t,'theta_s':theta_s,
            'thetaE':theta_e,'thetaB':theta_b,
            'Ws':1/theta_s,'We':1/theta_e,'Wb':1/theta_b,
            'alpha':alpha,'beta':beta,'A':A,'B':B,'lambda':lam}


def diag_inverse_6(r):
    return tuple(tuple((r['We'] if i<3 else r['Wb']) if i==j else F()
                       for j in range(6)) for i in range(6))


def _scale(a,z):
    return tuple(tuple(rat(z)*v for v in row) for row in a)


def _add(a,b):
    return tuple(tuple(v+w for v,w in zip(row,col)) for row,col in zip(a,b))


def _forms_background():
    return tuple(tuple(F(i==j+3) for i in range(6)) for j in range(3))


def _metric_tt(cross=False):
    return metric_tensor_mode(cross)


def _matter_oneforms(cross=False):
    z=(F(),F(),F(),F())
    if cross:
        return ((F(),F(1),F(),F()),(F(),F(),F(-1),F()),z)
    return ((F(),F(),F(-1),F()),(F(),F(-1),F(),F()),z)


def _dforms(xi,amplitudes):
    return tuple(wave_field_strength(xi,a) for a in amplitudes)


def _metric_jet(xi,h,beta):
    return _scale(wave_riemann_pair(xi,h),-beta)


def _matter_jet(df,alpha):
    f=_forms_background()
    gram=gram_first(f,df)
    return tuple(tuple(alpha*gram[i][j]*S[j] for j in range(6))
                 for i in range(6))


def _matter_second(df,dg,alpha):
    """Mixed Hessian of source Gram, with independent E and B variations."""
    gram=tuple(tuple(sum((u[i]*v[j]+v[i]*u[j] for u,v in zip(df,dg)),F())
                     for j in range(6)) for i in range(6))
    return tuple(tuple(alpha*gram[i][j]*S[j] for j in range(6))
                 for i in range(6))


def _trace_product(W,left,right):
    return trace(mul(mul(mul(W,left),W),right))


def _vector_ricci_hessian(xi,h,k,r):
    """Direct full 4x4 1-form Ricci contraction, TT scalar trace is zero."""
    rh,scalarh=linearized_ricci(xi,h)
    rk,scalark=linearized_ricci(xi,k)
    if scalarh or scalark:
        raise AssertionError('only TT modes admitted')
    inv=(1/r['theta_t'],1/r['theta_s'],1/r['theta_s'],1/r['theta_s'])
    return r['beta']**2*sum((inv[i]*inv[j]*ETA[i]*ETA[j]*rh[i][j]*rk[j][i]
                              for i in range(4) for j in range(4)),F())


def source_tensor_matrix(omega,p=1,*,lam=DEFAULT_LAMBDA,
                         alpha=DEFAULT_ALPHA,beta=DEFAULT_BETA,
                         A=DEFAULT_A,B=DEFAULT_B):
    """Exact 4x4 Hessian in h+,hX,a+,aX from three source multiplets.

    Full six-dimensional E/B bivector pair operator and full 1-form
    Ricci TT variation. The scalar/matter one-form background jets
    are zero, and transverse spin-two one-form variations have
    delta(delta_D omega)=0, so their Λ0 principal is zero.
    """
    r=source_responses(lam=lam,alpha=alpha,beta=beta,A=A,B=B)
    xi=(rat(omega),F(),F(),rat(p))
    W=diag_inverse_6(r)
    h=tuple(_metric_tt(cross) for cross in (False,True))
    a=tuple(_dforms(xi,_matter_oneforms(cross)) for cross in (False,True))
    pr=tuple(_metric_jet(xi,hmode,r['beta']) for hmode in h)
    pm=tuple(_matter_jet(dforms,r['alpha']) for dforms in a)
    out=[[F() for _ in range(4)] for _ in range(4)]
    for i in range(2):
        for j in range(2):
            out[i][j]=_trace_product(W,pr[i],pr[j])+_vector_ricci_hessian(xi,h[i],h[j],r)
            out[i][j+2]=out[j+2][i]=_trace_product(W,pr[i],pm[j])
            out[i+2][j+2]=_trace_product(W,pm[i],pm[j])-trace(
                mul(W,_matter_second(a[i],a[j],r['alpha'])))
    return tuple(tuple(row) for row in out)


def closed_entries(omega,p=1,*,lam=DEFAULT_LAMBDA,
                   alpha=DEFAULT_ALPHA,beta=DEFAULT_BETA,
                   A=DEFAULT_A,B=DEFAULT_B):
    """Independent closed-form tensor entries; no shared 6x6 trace code."""
    r=source_responses(lam=lam,alpha=alpha,beta=beta,A=A,B=B)
    alpha,beta,ws,we,wb=r['alpha'],r['beta'],r['Ws'],r['We'],r['Wb']
    w2=rat(omega)**2;p2=rat(p)**2
    delta=w2-p2
    q=we*w2-wb*p2
    hh=beta**2*(ws**2*delta**2/F(2)+2*q**2)
    hm=4*alpha*beta*wb*rat(p)*q
    mm=4*alpha*(2*alpha*wb**2*p2-alpha*wb*we*w2-wb*p2+we*w2)
    return (hh,hm,mm)


def check_closed_pencil(omega,p=1,**kw):
    hh,hm,mm=closed_entries(omega,p,**kw)
    m=source_tensor_matrix(omega,p,**kw)
    want=((hh,F(),hm,F()),(F(),hh,F(),hm),
          (hm,F(),mm,F()),(F(),hm,F(),mm))
    if m!=want:
        raise AssertionError('full bivector/one-form source trace != closed tensor coefficients')
    if det(m)!=(hh*mm-hm*hm)**2:
        raise AssertionError('two-helicity real determinant is not a square')
    return {'matrix':m,'one_helicity':((hh,hm),(hm,mm)),
            'one_helicity_det':hh*mm-hm*hm,
            'two_helicity_det':det(m),
            'SO2_closed_inside_trial':True}


def cubic_coefficients(*,lam=DEFAULT_LAMBDA,alpha=DEFAULT_ALPHA,
                       beta=DEFAULT_BETA,A=DEFAULT_A,B=DEFAULT_B):
    """p=1, exact cubic det P(x) where x=omega², with no interpolation."""
    r=source_responses(lam=lam,alpha=alpha,beta=beta,A=A,B=B)
    alpha,beta,ws,we,wb=r['alpha'],r['beta'],r['Ws'],r['We'],r['Wb']
    a=beta**2*ws**2/F(2)
    hh=(a+2*beta**2*wb**2,-2*a-4*beta**2*we*wb,a+2*beta**2*we**2)
    hm=(-4*alpha*beta*wb**2,4*alpha*beta*wb*we)
    mm=(4*alpha*(2*alpha*wb**2-wb),4*alpha*(we-alpha*wb*we))
    def prod(u,v):
        result=[F() for _ in range(len(u)+len(v)-1)]
        for i,x in enumerate(u):
            for j,y in enumerate(v):result[i+j]+=x*y
        return result
    hhm=prod(hh,mm);hms=prod(hm,hm)
    return tuple(u-(hms[i] if i<len(hms) else F()) for i,u in enumerate(hhm))


def source_jordan_reference():
    """Exact pinned p=1 source pencil and a length-two Jordan chain."""
    r=source_responses()
    if r['We']!=r['Wb'] or r['Ws']!=F(125,122):
        raise AssertionError('pinned source cone matching shifted')
    hh,hm,mm=closed_entries(F(2))
    # Record coefficients independent of this sample by 0,1,2 evaluations.
    c=cubic_coefficients()
    factor=F(75,14075583041536)
    a,b=F(1154113),F(1158253)
    expected=( -factor*b, factor*(a+2*b),
               -factor*(2*a+b),factor*a )
    if c!=expected:
        raise AssertionError('exact source Jordan polynomial differs from factorization')
    if closed_entries(0)!=(F(58525,228856384),F(-15,61504),F(-1470,61504)):
        raise AssertionError('tensor source normalization mismatch')
    if closed_entries(1)!=(F(),F(),F(9,61504)):
        raise AssertionError('old lightcone rank must be one')
    # The root has det multiplicity two, but matrix nullity exactly one.
    if evaluate_polynomial(c,F(1)) or c[1]+2*c[2]+3*c[3]:
        raise AssertionError('matched null root is not repeated')
    if 2*c[2]+6*c[3]==0:
        raise AssertionError('repeated root has multiplicity above two')
    # P'(1)v0+P(1)v1=0 for v0=(1,0), v1=(0,-10/3).
    k=F(15,61504)
    g=F(9,61504)
    v1= -2*k/g
    if v1!=F(-10,3) or 2*k+g*v1:
        raise AssertionError('nontrivial polynomial Jordan chain missing')
    return {'head_root':F(1),'extra_root':b/a,'cubic_coefficients':c,
            'det_factor_coefficient':factor,'det_linear_factor':(a,b),
            'at_root_rank':1,'root_multiplicity':2,'jordan_v0':(F(1),F()),
            'jordan_v1':(F(),v1),'regular_temporal_pencil':True}


def detuned_reference(eps=F(1,1000)):
    """Positive cubic discriminant and three exact positive root brackets."""
    eps=rat(eps)
    if eps not in (F(1,1000),F(-1,1000)):
        raise ValueError('registered rational detuning witnesses only')
    coeff=cubic_coefficients(lam=1+eps)
    disc=cubic_discriminant(coeff)
    if disc<=0:
        raise AssertionError('detuned cubic lacks distinct real roots')
    if eps>0:
        windows=((F(999987,1000000),F(999989,1000000)),
                 (F(999995,1000000),F(999997,1000000)),
                 (F(1003587,1000000),F(1003589,1000000)))
    else:
        windows=((F(1000003,1000000),F(1000005,1000000)),
                 (F(1000011,1000000),F(1000013,1000000)),
                 (F(1003585,1000000),F(1003588,1000000)))
    for a,b in windows:
        if not (a>0 and a<b and evaluate_polynomial(coeff,a)*evaluate_polynomial(coeff,b)<0):
            raise AssertionError('exact positive squared-speed brackets failed')
    return {'eps':eps,'discriminant':disc,'root_brackets':windows,
            'three_distinct_positive_x':True}


def leading_detuning_slopes():
    """Exact tangent cone for two roots x=1+k*eps+O(eps²).

    With lambda=1+eps, WB=W-alpha*W²*eps+O(eps²). The two
    coalescent roots solve
      (Ws²/2)*k² - 2*W²*(k+alpha*W)² = 0.
    This is a local necessary polynomial blow-up; root existence for
    nonzero eps is separately checked by exact sign brackets.
    """
    r=source_responses()
    ws,w,alpha=r['Ws'],r['We'],r['alpha']
    if w!=r['Wb'] or ws==2*w:
        raise AssertionError('distinct real tangent slopes require matched reference')
    k1=-2*alpha*w*w/(2*w-ws)
    k2=-2*alpha*w*w/(2*w+ws)
    if k1==k2:
        raise AssertionError('the tangent slopes must be distinct')
    for k in (k1,k2):
        if (ws*ws/F(2))*k*k-2*w*w*(k+alpha*w)**2:
            raise AssertionError('blown-up double-root quadratic mismatch')
    if set((k1,k2))!={F(-61,4960),F(-183,45632)}:
        raise AssertionError('exact detuning tangent slope values changed')
    return {'steep':k1,'shallow':k2,'two_distinct_real_tangents':True}


def scalar_longitudinal_response(omega=0,p=1):
    """Source scalar-sector derivative rejects a YM-style Gauss quotient.

    An independent one-form delta omega proportional to k has d omega=0
    but delta_D omega = -k^mu a_mu nonzero for generic non-null k.
    Source M_(0)=|D Phi_(0)|² produces Hessian -2 alpha/theta0 *s².
    Here real formal derivative conventions are retained.
    """
    r=source_responses()
    omega,p=rat(omega),rat(p)
    norm=-omega**2+p**2
    dflat=F()  # k wedge k=0
    scalar=-2*r['alpha']/r['theta0']*norm**2
    return {'domega_bivector_norm':dflat,'coderivative':norm,
            'scalar_H':scalar,'full_D_gauge_quotient_available':False}


def reference_experiment():
    j=source_jordan_reference()
    slopes=leading_detuning_slopes()
    plus=detuned_reference(F(1,1000))
    minus=detuned_reference(F(-1,1000))
    for w,p in ((F(),F(1)),(F(1),F(1)),(F(3,2),F(2))):
        check_closed_pencil(w,p)
    return {'schema':'mathcan.toe17.triplet_tensor.v1',
            'matched_lightcone_jordan_chain':True,
            'matched_extra_squared_frequency':str(j['extra_root']),
            'detuned_plus_three_distinct_positive_roots':plus['three_distinct_positive_x'],
            'lightcone_detuning_slopes':(str(slopes['steep']),str(slopes['shallow'])),
            'detuned_minus_three_distinct_positive_roots':minus['three_distinct_positive_x'],
            'full_D_has_longitudinal_gauge':False,
            'source_triplet_background_on_shell':False,
            'full_matter_metric_hodge_variations_included':False,
            'physical_GfE_constraint_quotient_complete':False,
            'strong_hyperbolicity_verified':False}


if __name__=='__main__':
    import json
    print(json.dumps(reference_experiment(),sort_keys=True,indent=2))
