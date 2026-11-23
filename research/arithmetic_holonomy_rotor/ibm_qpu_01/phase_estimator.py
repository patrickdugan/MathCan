"""Four-phase Fourier response and conditional classical Fisher information."""
from __future__ import annotations
import numpy as np
from exact_oracle import PHASE_OFFSETS, four_phase_probabilities, real_fourier_coefficient


def wrap(angle):
    """Wrap signed angles to [-pi, pi)."""
    a = np.asarray(angle)
    return (a+np.pi)%(2*np.pi)-np.pi


def quadrature(p):
    """Accept shape (...,4) probabilities; complex first DFT quadrature."""
    return 0.5*np.sum(np.asarray(p)*np.exp(-1j*PHASE_OFFSETS),axis=-1)


def phase_from_quadrature(z,calibration_a1:float):
    if abs(calibration_a1)<1e-10: raise ValueError('First harmonic too small to estimate phase')
    return wrap(np.angle(np.asarray(z)/calibration_a1))


def jacobian_phase_prob(t:float,theta:float,step:float=1e-5):
    return (four_phase_probabilities(t,theta+step)-four_phase_probabilities(t,theta-step))/(2*step)


def phase_fisher_information(t:float,theta:float,total_shots:int,
                             nuisance:bool=False)->dict:
    """Independent Bernoulli observations; nuisance uses local baseline & cosine amplitude."""
    p=four_phase_probabilities(t,theta)
    deriv=jacobian_phase_prob(t,theta)
    shots=total_shots/4
    weights=shots/np.maximum(p*(1-p),1e-12)
    information=float(np.dot(weights,deriv**2))
    ret={'known_response_fisher':information,'known_response_crlb_rad2':1/information}
    if nuisance:
        # At given theta, approximate the calibrated response by a+b cos(theta+delta).
        # Treat a,b as nuisance and differentiate the exact phi-dependent model in theta.
        J=np.column_stack([deriv,np.ones(4),np.cos(theta+PHASE_OFFSETS)])
        mat=J.T@(weights[:,None]*J)
        inverse=np.linalg.pinv(mat,rcond=1e-12)
        ret['nuisance_fisher_schur']=float(1/inverse[0,0])
        ret['nuisance_crlb_rad2']=float(inverse[0,0])
    return ret


def monte_carlo(t:float,theta:float,shots_total:int=8192,
                replicates:int=1000,seed:int=20261123,
                bitflip:float=0.,depolarizing:float=0.)->dict:
    """Phenomenological independent readout flips and global depolarization.

    This is not a hardware-calibrated Qiskit Aer noise model.
    """
    if shots_total%4: raise ValueError('Shots must divide equally into four settings')
    from hamiltonian import square_hamiltonian
    from exact_oracle import exact_probabilities
    from scipy.linalg import expm
    probabilities=[]
    for delta in PHASE_OFFSETS:
        states=exact_probabilities(square_hamiltonian(theta+delta),t)
        state_probs=(1-depolarizing)*states+depolarizing/4
        # Independent symmetric measurement flips on both physical qubits.
        p=float(sum(state_probs[x]*(bitflip if x&1 else 1-bitflip)*
                    (bitflip if x&2 else 1-bitflip) for x in range(4)))
        probabilities.append(p)
    probabilities=np.array(probabilities)
    a1=real_fourier_coefficient(t)
    rng=np.random.default_rng(seed)
    samples=rng.binomial(shots_total//4,probabilities,size=(replicates,4))/(shots_total//4)
    z=quadrature(samples)
    est=phase_from_quadrature(z,a1)
    err=wrap(est-theta)
    return {'seed':seed,'shots_total':shots_total,'replicates':replicates,
            'bitflip':bitflip,'depolarizing':depolarizing,
            'estimated_p':probabilities.tolist(),'calibration_a1':a1,
            'mean_circular_bias_rad':float(np.angle(np.mean(np.exp(1j*err)))),
            'rmse_rad':float(np.sqrt(np.mean(err**2))),
            'rmse_deg':float(np.degrees(np.sqrt(np.mean(err**2)))),
            'abs_error_95pct_deg':float(np.degrees(np.quantile(abs(err),.95)))}


def ci_wilson(success:int,shots:int,z:float=1.959963984540054):
    p=success/shots
    mid=(p+z*z/(2*shots))/(1+z*z/shots)
    radius=z*np.sqrt(p*(1-p)/shots+z*z/(4*shots*shots))/(1+z*z/shots)
    return (float(mid-radius),float(mid+radius))
