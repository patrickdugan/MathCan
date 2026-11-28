"""Shot budgeting in the prespecified four Bernoulli return measurements."""
from __future__ import annotations
import math
import numpy as np
from phase_estimator import phase_fisher_information
from exact_oracle import four_phase_probabilities,real_fourier_coefficient


def shot_targets(t=1.6,theta=.73,target_deg=5.,z_score=1.96):
    """Conditional known-response CRLB and approximate 95% CI width target.

    Fisher information scales linearly in B. Exact numerical p_j includes high harmonics.
    """
    one_shot=phase_fisher_information(t,theta,4,nuisance=False)['known_response_fisher']/4
    sigma_target=math.radians(target_deg)/z_score
    b_needed=int(math.ceil(1/(one_shot*sigma_target*sigma_target)))
    b_needed=4*int(math.ceil(b_needed/4))
    return {'time':t,'theta':theta,'target_half_width_deg':target_deg,
            'confidence_z':z_score,'needed_total_shots_crlb':b_needed,
            'shots_per_phase':b_needed//4,'fisher_per_shot':one_shot,
            'scope':'Local asymptotic CRLB; assumes calibrated response and independent Bernoulli observations'}


def leading_order_bound(length:int,t:float,shots:int,degree:int=2,j:float=1.):
    """AHR-07 small-time variance bound for J=1 uniform cycle."""
    import math
    beta=4*((-1)**(length//2))*j**length/math.factorial(length)
    kappa=degree*j*j
    return {'cycle_length':length,'leading_variance_rad2':2*kappa/(shots*beta*beta*t**(2*length-2)),
            'prefactor_beta':beta}
