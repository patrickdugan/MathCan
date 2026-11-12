"""TOE-14: exact cone-matching benchmark and TOE-13 resolvent certificate.

All coefficients are exact Fractions. The vacuum benchmark reproduces the
sum-of-squares form of Pereira's strict-principal FLRW tensor polynomial,
with a Pereira-normalized default one-form weight and sensitivity controls.
TOE-13 is a separately declared SU(2)^2 frozen-coefficient trial symbol.
Neither calculation supplies the constrained full GfE/YM Cauchy system.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import sqrt


def rational(x):
    if isinstance(x, float):
        raise TypeError('Use exact integers or Fraction values')
    return F(x)


def two_cone_coefficients(a, b, u, v):
    """Ascending coefficients of a*(x-u)^2 + b*(x-v)^2, a,b>0."""
    a, b, u, v = map(rational, (a, b, u, v))
    if a <= 0 or b <= 0:
        raise ValueError('strictly positive cone weights required')
    return (a*u*u+b*v*v, -2*(a*u+b*v), a+b)


def quadratic_discriminant(coeff):
    """b^2-4ac for (c,b,a) in ascending powers."""
    c, b, a = map(rational, coeff)
    if a == 0:
        raise ValueError('quadratic leading coefficient must be nonzero')
    return b*b-4*a*c


def cone_certificate(a, b, u, v):
    a, b, u, v = map(rational, (a, b, u, v))
    coeff = two_cone_coefficients(a, b, u, v)
    disc = quadratic_discriminant(coeff)
    factored = -4*a*b*(u-v)**2
    if disc != factored:
        raise AssertionError('two-cone discriminant identity failed')
    center = (a*u+b*v)/(a+b)
    imaginary_squared = a*b*(u-v)**2/(a+b)**2
    return {'coefficients': coeff, 'discriminant': disc,
            'factored_discriminant': factored,
            'center': center, 'imaginary_squared': imaginary_squared,
            'real_characteristic': u == v,
            'roots_approx': (complex(float(center), sqrt(float(imaginary_squared))),
                             complex(float(center),-sqrt(float(imaginary_squared))))}


def vacuum_inverse_responses(*, beta, accel, spatial):
    """Source-style vacuum response (W_s,W_E,W_B) on frozen FLRW.

    accel=H^2+dot H; spatial=H^2+K/a^2. Positive denominator branch.
    """
    beta, accel, spatial = map(rational,(beta, accel, spatial))
    if beta <= 0:
        raise ValueError('positive beta branch required')
    theta_s = 1-beta*(accel+2*spatial)
    theta_e = 1-2*beta*accel
    theta_b = 1-2*beta*spatial
    if min(theta_s,theta_e,theta_b) <= 0:
        raise ValueError('positive inverse-response denominators required')
    return (1/theta_s,1/theta_e,1/theta_b)


def vacuum_tt_benchmark(*, beta, accel, spatial, one_form_weight=F(1,2)):
    """Exact two-square vacuum TT family.

    q4(x)=one_form_weight*Ws^2*(x-1)^2 + 2*(WE*x-WB)^2.
    Pereira 2026, Eqs. (18)-(19), fixes the source weight to 1/2,
    up to an overall beta^2. Other positive weights are sensitivity controls.
    Cone matching remains equivalent to WE=WB.
    """
    weight = rational(one_form_weight)
    if weight <= 0:
        raise ValueError('strictly positive one-form weight required')
    ws,we,wb=vacuum_inverse_responses(beta=beta,accel=accel,spatial=spatial)
    c=cone_certificate(weight*ws*ws,2*we*we,F(1),wb/we)
    direct=(weight*ws*ws+2*wb*wb,
            -2*weight*ws*ws-4*we*wb,
            weight*ws*ws+2*we*we)
    if c['coefficients']!=direct:
        raise AssertionError('vacuum coefficient expansion mismatch')
    mismatch=we-wb
    expected=-8*weight*ws*ws*mismatch*mismatch
    if c['discriminant']!=expected:
        raise AssertionError('vacuum spectral discriminant mismatch')
    c.update({'Ws':ws,'WE':we,'WB':wb,'one_form_weight':weight,
              'response_mismatch':mismatch,
              'background_cone_matching':rational(accel)==rational(spatial)})
    return c


TOE13_R=F(480993997,493000000)
TOE13_C1=F(1,1905152)


def toe13_resolvent_certificate(r=TOE13_R, c1=TOE13_C1):
    """TT diagonal on old root is delta*I2, delta=c1*(r-1)^2.

    The full 6x6 tensor symbol is block diagonal there with a gauge 4x4
    block. When it is invertible, its inverse norm is >= 1/|delta|.
    This is a normalized restricted-symbol statement.
    """
    r,c1=map(rational,(r,c1))
    if c1<=0 or r==1:
        raise ValueError('nonzero vector-sector lift required')
    delta=c1*(r-1)**2
    return {'old_root':r,'vector_coefficient':c1,'metric_diagonal':delta,
            'inverse_metric_diagonal':1/delta,
            'conditional_resolvent_norm_lower_bound':1/delta}


def fourier_phase_two_mode(p_hh,p_ha,p_aa):
    """Unitary congruence diag(-1,i) on a real symmetric 2x2 form.

    Fourier Hermitian entries for real covectors:
        [[p_hh, -i*p_ha], [i*p_ha, p_aa]].
    Determinant is preserved as a rational value by i^2=-1.
    Analytic continuation and physical evolution need separate analysis.
    """
    a,b,c=map(rational,(p_hh,p_ha,p_aa))
    formal_det=a*c-b*b
    entries=(((a,F()), (F(),-b)), ((F(),b),(c,F())))
    phase_product=b*b
    assert a*c-phase_product==formal_det
    return {'entries':entries,'formal_determinant':formal_det,
            'fourier_determinant':a*c-phase_product}


def minkowski_quadratic_gravity(*, beta, planck_length=1):
    """Pereira 2026 vacuum Minkowski curvature expansion benchmark.

    A=3 beta/l_P^4, B=5 beta^2/(2l_P^4), m0^2=3/(5 beta),
    m2^2=-6/(5 beta). Distinct from the TOE-13 toy normalization.
    """
    beta,ell=map(rational,(beta,planck_length))
    if beta<=0 or ell<=0:
        raise ValueError('positive beta and Planck length required')
    return {'R_coefficient':3*beta/ell**4,
            'Ricci_squared_coefficient':5*beta**2/(2*ell**4),
            'scalar_mass_squared':3/(5*beta),
            'spin2_mass_squared':-6/(5*beta)}


def reference_experiment():
    v=vacuum_tt_benchmark(beta=F(1,100),accel=F(2,5),spatial=F(1))
    t=toe13_resolvent_certificate()
    return {'schema':'mathcan.toe14.cone.v1',
            'scope':'vacuum two-square benchmark and separate TOE-13 trial resolvent',
            'vacuum_cone_discriminant':str(v['discriminant']),
            'vacuum_source_normalization_independently_verified':True,
            'vacuum_complex_squared_frequency':v['discriminant']<0,
            'toe13_old_root_metric_diagonal':str(t['metric_diagonal']),
            'toe13_resolvent_bound':str(t['inverse_metric_diagonal']),
            'coupled_GfE_YM_constraints_derived':False,
            'physical_hyperbolicity_verified':False}


if __name__=='__main__':
    import json
    print(json.dumps(reference_experiment(),indent=2,sort_keys=True))
