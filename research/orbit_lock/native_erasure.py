"""OLM-15 exact rational native SAE contribution erasure witnesses.

Everything here is a finite Fraction computation; no external dependencies.
"""
from fractions import Fraction as Q


def rat(x):
    return x if isinstance(x, Q) else Q(x)


def symmetric_response(f, h, r):
    h, r = rat(h), rat(r)
    if r <= 0:
        raise ValueError("positive finite-difference radius required")
    return (f(h+r)-f(h-r))/(2*r)


def native_drop(f, h, coefficient, decoder):
    h, coefficient, decoder = rat(h), rat(coefficient), rat(decoder)
    if coefficient < 0:
        raise ValueError("SAE coefficient must be nonnegative")
    return f(h)-f(h-coefficient*decoder)


def curvature_obstruction(k=3, radius=Q(1, 5)):
    k, radius = rat(k), rat(radius)
    if k <= 1 or radius <= 0:
        raise ValueError("choose curvature K>1 and radius>0")
    C = Q(10)
    f = lambda x: C+x
    g = lambda x: C+x+k*(x-1)**2
    return {
        "clean_feature": Q(1),
        "clean_margin_A": f(Q(1)),
        "clean_margin_B": g(Q(1)),
        "central_A": symmetric_response(f, 1, radius),
        "central_B": symmetric_response(g, 1, radius),
        "native_drop_A": native_drop(f, 1, 1, 1),
        "native_drop_B": native_drop(g, 1, 1, 1),
        "erased_margin_A": f(Q(0)),
        "erased_margin_B": g(Q(0)),
    }


def stable_selected_residual(clean_coefficient, gain):
    """Formula only for a positive and still-selected linear ReLU atom."""
    z, g = rat(clean_coefficient), rat(gain)
    if z <= 0 or g < 0 or g > 1:
        raise ValueError("stable positive selection requires z>0 and 0<=gain<=1")
    return z*(1-g)


def erasure_taylor_bound(coefficient, decoder_norm_squared, hessian_bound):
    z = rat(coefficient)
    dd = rat(decoder_norm_squared)
    M = rat(hessian_bound)
    if z < 0 or dd < 0 or M < 0:
        raise ValueError("nonnegative coefficient, norm and curvature required")
    return M*z*z*dd/2


def two_teacher_bound(derivative_mismatch, zA, dA_squared, MA,
                      zB, dB_squared, MB, alpha):
    eps, alpha = rat(derivative_mismatch), rat(alpha)
    if eps < 0 or alpha < 0:
        raise ValueError("nonnegative derivative mismatch and scale")
    return (eps + erasure_taylor_bound(zB, dB_squared, MB) +
            alpha*erasure_taylor_bound(zA, dA_squared, MA))


def quadratic_sharpness(a=2, b=3):
    a, b = rat(a), rat(b)
    f = lambda x: a*x+b*x*x/2
    h = Q(1)
    drop = native_drop(f,h,1,1)
    linear = a+b
    error = abs(drop-linear)
    bound = erasure_taylor_bound(1,1,abs(b))
    assert error == bound
    return {"native_drop":drop,"clean_derivative":linear,
            "difference":error,"bound":bound}


def active_but_unnecessary():
    h = (Q(1),Q(1))
    erased = (Q(0),Q(1))
    m = lambda x: Q(10)+x[1]
    return {"clean_activation":h[0],"erased_hidden":erased,
            "margin_drop":m(h)-m(erased)}


if __name__ == "__main__":
    import json
    def encode(x):
        if isinstance(x,Q):return str(x)
        if isinstance(x,tuple):return list(map(str,x))
        raise TypeError(type(x))
    print(json.dumps({"obstruction":curvature_obstruction(),
                      "sharp":quadratic_sharpness(),
                      "active_without_necessity":active_but_unnecessary()},
                     default=encode,indent=2))
