"""Exhaustive AHR-06 16-mask control under matched TOTAL shots."""
from __future__ import annotations
import numpy as np
from scipy.linalg import expm
from exact_oracle import PHASE_OFFSETS, four_phase_probabilities,real_fourier_coefficient
from phase_estimator import quadrature,phase_from_quadrature,wrap
from hamiltonian import square_hamiltonian

EDGES=((0,1),(0,2),(2,3),(1,3))


def masked_prob(phase:float,t:float,mask:int):
    h=square_hamiltonian(phase)
    for i,(u,v) in enumerate(EDGES):
        if not (mask>>i)&1: h[u,v]=h[v,u]=0
    return float(abs(expm(-1j*h*t)[0,0])**2)


def mask_probabilities(t:float,theta:float):
    return np.array([[masked_prob(theta+ph,t,m) for m in range(16)] for ph in PHASE_OFFSETS])


def parity_weights():
    return np.array([(-1)**(4-int(m).bit_count()) for m in range(16)])


def four_phase_mask_identity(t:float,theta:float):
    matrix=mask_probabilities(t,theta)
    masked_quadrature=quadrature(matrix@parity_weights())
    full=quadrature(four_phase_probabilities(t,theta))
    return {'masked':masked_quadrature,'full':full,
            'absolute_discrepancy':float(abs(masked_quadrature-full))}


def equal_budget_comparison(t:float=1.6,theta:float=.73,total_shots:int=8192,
                             replicates:int=1000,seed:int=20261123):
    """Fixed total B across 4 intact and 64 masked (16*4) settings."""
    if total_shots%64: raise ValueError('Budget must divide into 64 mask-by-phase cells')
    rng=np.random.default_rng(seed)
    intact_p=four_phase_probabilities(t,theta)
    masks_p=mask_probabilities(t,theta)
    a1=real_fourier_coefficient(t)
    a=rng.binomial(total_shots//4,intact_p,size=(replicates,4))/(total_shots//4)
    b=rng.binomial(total_shots//64,masks_p,size=(replicates,4,16))/(total_shots//64)
    z_a=quadrature(a)
    z_b=quadrature(b@parity_weights())
    err_a=wrap(phase_from_quadrature(z_a,a1)-theta)
    err_b=wrap(phase_from_quadrature(z_b,a1)-theta)
    return {'total_shots':total_shots,'shots_per_intact_setting':total_shots//4,
            'shots_per_mask_setting':total_shots//64,
            'phase_settings_intact':4,'phase_settings_masked':64,
            'intact_rmse_deg':float(np.degrees(np.sqrt(np.mean(err_a**2)))),
            'masked_rmse_deg':float(np.degrees(np.sqrt(np.mean(err_b**2)))),
            'ideal_quadrature_discrepancy':four_phase_mask_identity(t,theta)['absolute_discrepancy']}
