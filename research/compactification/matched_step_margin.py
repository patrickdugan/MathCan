"""NRF-09 exact rational path attribution and robust eight-arm median bounds."""
from fractions import Fraction as Q

def margin_decomposition(m16_u32, m32_u16, m32_u32):
    m16, m3216, m3232 = map(Q, (m16_u32, m32_u16, m32_u32))
    exposure_gap = m3216 - m16
    matched_gap = m3232 - m16
    training_lag = m3216 - m3232
    assert exposure_gap == matched_gap + training_lag
    return exposure_gap, matched_gap, training_lag

def score(error, leakage, lam):
    e, l, lam = map(Q, (error, leakage, lam))
    if min(e, l, lam) < 0:
        raise ValueError("nonnegative loss, leakage and penalty needed")
    return e + lam*l*l

def median8(values):
    if len(values) != 8:
        raise ValueError("exactly eight complete random controls needed")
    v = sorted(map(Q, values))
    return (v[3] + v[4])/2

def signed_margin(supervised, random_arms, lam):
    if len(random_arms) != 8:
        raise ValueError("eight matched controls needed")
    return score(*supervised, lam) - median8(
        [score(*a, lam) for a in random_arms])

def score_drift_bound(old_error, old_leakage, new_error, new_leakage, lam):
    E, L, Ep, Lp, lam = map(Q, (
        old_error, old_leakage, new_error, new_leakage, lam))
    if min(E, L, Ep, Lp, lam) < 0:
        raise ValueError("nonnegative arguments required")
    dE, dL = abs(Ep-E), abs(Lp-L)
    return dE + lam*dL*(2*L+dL)

def certified_margin_drift(old_sup, new_sup, old_controls, new_controls, lam):
    if len(old_controls) != 8 or len(new_controls) != 8:
        raise ValueError("eight matched control arms needed")
    sup = score_drift_bound(*old_sup, *new_sup, lam)
    random = max(score_drift_bound(*a, *b, lam)
                 for a, b in zip(old_controls, new_controls))
    return sup + random

def certified_sign(old_margin, drift_bound):
    m, bound = Q(old_margin), Q(drift_bound)
    if bound < 0:
        raise ValueError("nonnegative bound needed")
    if m > bound:
        return 1
    if m < -bound:
        return -1
    return 0
