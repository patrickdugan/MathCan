"""Independent dense-matrix oracle for signed cycle return probabilities."""
from __future__ import annotations
import numpy as np
from scipy.linalg import expm
from hamiltonian import square_hamiltonian

PHASE_OFFSETS = np.arange(4, dtype=float) * np.pi / 2


def exact_probabilities(h: np.ndarray,t: float, start: int=0) -> np.ndarray:
    evolution=expm(-1j*t*h)
    return np.abs(evolution[:,start])**2


def return_probability(t:float,phase:float,broken:bool=False,
                       detuning:float=0.,j:float=1.) -> float:
    return float(exact_probabilities(square_hamiltonian(phase,j,broken,detuning),t)[0])


def four_phase_probabilities(t:float,theta:float,broken:bool=False,
                             detuning:float=0.,j:float=1.) -> np.ndarray:
    return np.array([return_probability(t,theta+delta,broken,detuning,j)
                     for delta in PHASE_OFFSETS])


def real_fourier_coefficient(t:float,n:int=1,samples:int=256,
                             broken:bool=False,detuning:float=0.,j:float=1.) -> float:
    phases=np.arange(samples)*2*np.pi/samples
    return float(2*np.mean([return_probability(t,p,broken,detuning,j)*np.cos(n*p)
                            for p in phases]))


def equivalent_up_to_phase(u:np.ndarray,v:np.ndarray,tol:float=1e-10)->bool:
    z=np.vdot(u,v)
    if abs(z)<1e-15: return False
    return bool(np.linalg.norm(u-(z.conjugate()/abs(z))*v)<tol)
