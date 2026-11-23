#!/usr/bin/env python3
"""AHR-01: exact arithmetic-holonomy rotor benchmarks (numpy/scipy only).

Two-qubit basis: |xy> has array index 2*x + y. Arithmetic labels n=2**x * 3**y.
All outputs are classical calculations; this script DOES NOT submit IBM QPU jobs.
"""
from __future__ import annotations

import csv
import json
import math
from pathlib import Path

import numpy as np
from scipy.linalg import expm

I = np.eye(2, dtype=np.complex128)
X = np.array([[0, 1], [1, 0]], dtype=np.complex128)
Y = np.array([[0, -1j], [1j, 0]], dtype=np.complex128)
Z = np.diag([1, -1]).astype(np.complex128)
n = (I - Z) / 2
START = np.array([1, 0, 0, 0], dtype=np.complex128)


def hamiltonian(phi: float, J: float = 1.0, delta: float = 0.0,
                break_cycle: bool = False, p: int = 2, q: int = 3) -> np.ndarray:
    """Peierls flux on the x=1, y-changing edge; delta shifts composite's log-energy."""
    a, b = math.log(p), math.log(q)
    # With break_cycle, remove the top x-transition, at y=1.
    h_horizontal = J * np.kron(X, I - n if break_cycle else I)
    h_vertical = J * (
        np.kron(I - n, X)
        + np.kron(n, math.cos(phi) * X + math.sin(phi) * Y)
    )
    h = (a * np.kron(n, I) + b * np.kron(I, n)
         + delta * np.kron(n, n) + h_horizontal + h_vertical)
    assert np.allclose(h, h.conj().T, atol=1e-13)
    return h


def quantum_state(phi: float, t: float, **kwargs) -> np.ndarray:
    return expm(-1j * t * hamiltonian(phi, **kwargs)) @ START


def observables(phi: float, t: float, **kwargs) -> tuple[float, float]:
    v = quantum_state(phi, t, **kwargs)
    p_return = float(abs(v[0]) ** 2)
    concurrence = float(2 * abs(np.linalg.det(v.reshape(2, 2))))
    return p_return, concurrence


def pauli_terms(phi: float, J: float = 1.0, p: int = 2, q: int = 3):
    """Trace-free H as (coefficient, matrix). Global phase omitted.

    For Qiskit with x=q0 and y=q1 (little-endian), labels are:
    Zx='IZ', Zy='ZI', Xx='IX', Xy='XI', ZxXy='XZ', Yy='YI', ZxYy='YZ'.
    """
    c, s = math.cos(phi), math.sin(phi)
    return [
        (-0.5 * math.log(p), np.kron(Z, I)),
        (-0.5 * math.log(q), np.kron(I, Z)),
        (J, np.kron(X, I)),
        (0.5 * J * (1 + c), np.kron(I, X)),
        (0.5 * J * (1 - c), np.kron(Z, X)),
        (0.5 * J * s, np.kron(I, Y)),
        (-0.5 * J * s, np.kron(Z, Y)),
    ]


def suzuki2(phi: float, t: float, steps: int) -> np.ndarray:
    """Second-order symmetric product formula, for classical Trotter preflight."""
    h_terms = [c * m for c, m in pauli_terms(phi) if abs(c) > 1e-12]
    half_step = np.eye(4, dtype=np.complex128)
    for h in h_terms:
        half_step = half_step @ expm(-1j * t * h / (2 * steps))
    step = half_step
    for h in reversed(h_terms):
        step = step @ expm(-1j * t * h / (2 * steps))
    return np.linalg.matrix_power(step, steps)


def validations():
    # Checks of arithmetic log-energy curvature.
    a, b = math.log(2), math.log(3)
    assert abs(math.log(6) - a - b) < 1e-14
    # Exact spectral invariants for any flux and arbitrary spectral variable.
    h0 = hamiltonian(0)
    for phi in (math.pi/4, math.pi/2, math.pi):
        h = hamiltonian(phi)
        for k in (1, 2, 3):
            assert abs(np.trace(np.linalg.matrix_power(h, k))
                       - np.trace(np.linalg.matrix_power(h0, k))) < 1e-10
        fourth = (np.trace(np.linalg.matrix_power(h, 4))
                  - np.trace(np.linalg.matrix_power(h0, 4)))
        assert abs(fourth - 8 * (math.cos(phi) - 1)) < 1e-10
        for lam in (0, 0.5, 1.2, 2.8):
            difference = (np.linalg.det(lam*np.eye(4) - h)
                          - np.linalg.det(lam*np.eye(4) - h0))
            assert abs(difference - 2 * (1 - math.cos(phi))) < 1e-10
    # Product dynamics when zero flux.
    for t in (0.4, 0.8, 1.6):
        assert observables(0, t)[1] < 1e-12
        tree_ps = [observables(phi, t, break_cycle=True)[0]
                   for phi in (0, math.pi/2, math.pi)]
        assert max(tree_ps) - min(tree_ps) < 1e-12
    # Return probability leading t^4 coefficient.
    t = 0.01
    dp = observables(math.pi, t)[0] - observables(0, t)[0]
    leading = -t**4 / 3
    assert abs(dp/leading - 1) < 2e-4
    # Concurrence leading t^2 coefficient.
    t = 0.001
    c = observables(math.pi, t)[1]
    assert abs(c/(2*t*t) - 1) < 1e-3
    # Decomposition consistency for nonzero flux (up to identity).
    for phi in (0, math.pi/2, math.pi):
        reconstructed = sum(c * op for c, op in pauli_terms(phi))
        expected = hamiltonian(phi) - (a+b)/2 * np.eye(4)
        assert np.allclose(reconstructed, expected, atol=1e-12)


def main():
    validations()
    output = Path(__file__).resolve().parent
    rows = []
    for t in [0.2, 0.4, 0.6, 0.8, 1.0, 1.2, 1.4, 1.6, 2.0]:
        for phi, label in [(0., '0'), (math.pi/2, 'pi/2'), (math.pi, 'pi')]:
            p0, concurrence = observables(phi, t)
            rows.append(dict(time=t, flux=label, p_return=p0,
                             pure_concurrence=concurrence))
    csvpath = output/'ahr01_ideal_predictions.csv'
    with csvpath.open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    diagnostics = dict(
        tests='PASS',
        model='AHR-01',
        qubits=2,
        J=1.0,
        energy_2=math.log(2),
        energy_3=math.log(3),
        observations={str(t): {
            label: dict(return_probability=observables(phi,t)[0],
                        pure_concurrence=observables(phi,t)[1])
            for phi, label in [(0.,'zero'), (math.pi/2,'half'), (math.pi,'pi')]}
            for t in (0.8, 1.0, 1.6)},
        trotter_second_order=[dict(
            flux=label, time=t, reps=reps,
            ideal_return=observables(phi,t)[0],
            approx_return=float(abs((suzuki2(phi,t,reps) @ START)[0])**2),
            return_error=abs(float(abs((suzuki2(phi,t,reps) @ START)[0])**2)
                             - observables(phi,t)[0]))
            for phi,label in [(math.pi/2,'half'),(math.pi,'pi')]
            for t in (0.8,1.6) for reps in (2,4,8)]
    )
    (output/'ahr01_validation.json').write_text(json.dumps(diagnostics, indent=2) + '\n')
    print('PASS: analytical identities, short-time expansion, broken-loop control')
    for t in (0.8, 1.6):
        print(f't={t}, P_0={observables(0,t)[0]:.6f}, '
              f'P_pi={observables(math.pi,t)[0]:.6f}, '
              f'C_pi={observables(math.pi,t)[1]:.6f}')
    print('Wrote', csvpath)
    print('Wrote', output/'ahr01_validation.json')

if __name__ == '__main__':
    main()