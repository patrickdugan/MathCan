"""AHR-QPU-01 arithmetic-square Hamiltonian, little endian: x=q0, y=q1."""
from __future__ import annotations
import numpy as np


def square_hamiltonian(phi: float, j: float = 1., broken: bool = False,
                       detuning: float = 0.) -> np.ndarray:
    """H on |0>,|1>,|2>,|3> = |00>,|10>,|01>,|11>.

    The y flip conditioned on x=1 has H[3,1] = J exp(+i phi),
    implementing cos(phi)*Y_x-side flip + sin(phi)*PauliY_q1.
    Broken control deletes the (1,3) edge; remaining graph is a tree.
    """
    h = np.diag([0., np.log(2.), np.log(3.), np.log(6.) + detuning]).astype(complex)
    for u,v in ((0,1),(0,2),(2,3)):
        h[u,v] = h[v,u] = j
    if not broken:
        h[3,1] = j*np.exp(1j*phi)
        h[1,3] = np.conj(h[3,1])
    assert np.allclose(h, h.conj().T)
    return h


def hypercube_hamiltonian(d: int, edge_phases: dict[tuple[int,int],float],
                          primes: tuple[int,...]=(2,3,5),
                          j: float=1.) -> np.ndarray:
    """d-prime finite hypercube; phases oriented from lower to higher vertex."""
    if d > len(primes): raise ValueError('One prime needed per direction')
    n = 1 << d
    energies = [sum(np.log(primes[i]) for i in range(d) if (x>>i)&1) for x in range(n)]
    h = np.diag(energies).astype(complex)
    for a in range(n):
        for i in range(d):
            if (a>>i)&1: continue
            b = a | (1<<i)
            theta = edge_phases.get((a,b),0.)
            h[b,a] = j*np.exp(1j*theta)
            h[a,b] = np.conj(h[b,a])
    return h
