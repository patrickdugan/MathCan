"""Independent eigenvalue and exponential references for local return probabilities."""

from math import pi

import numpy as np
from scipy.linalg import expm

from hamiltonian import (
    ENERGIES,
    FULL_MASK,
    OFFSETS,
    PLANTED_PHASE,
    PRIMARY_TIME,
    masks,
    rephase,
    square,
)


def spectral_return(h, time, site=0):
    values, vectors = np.linalg.eigh(h)
    return float(abs(np.vdot(abs(vectors[site])**2, np.exp(-1j*time*values)))**2)


def direct_square(phi, energies=ENERGIES, mask=FULL_MASK, j=1.0):
    """Independent literal little-endian matrix, with AHR mask order."""
    a, b, c, d = energies
    x, y, closing, top = [j * flag for flag in mask]
    phase = closing * np.exp(1j * phi)
    return np.array([[a, x, y, 0], [x, b, 0, phase.conjugate()],
                     [y, 0, c, top], [0, phase, top, d]], dtype=complex)


def direct_return(h, time, site=0):
    return float(abs(expm(-1j*time*h)[site, site])**2)


def phase_scan(time, theta, offsets=OFFSETS, energies=ENERGIES, mask=FULL_MASK):
    return np.array([spectral_return(square(theta+delta, energies, mask), time) for delta in offsets])


def harmonic(probabilities):
    values = np.asarray(probabilities)
    n = values.shape[-1]
    if n < 3:
        raise ValueError("at least three equally spaced phase settings are required")
    kernel = 2*np.exp(-2j*pi*np.arange(n)/n)/n
    return values @ kernel


def cosine_coefficients(time, *, orders=12, n=256, energies=ENERGIES):
    nodes = np.arange(n)*2*pi/n
    coefficients = np.fft.fft(phase_scan(time, 0, nodes, energies)) / n
    return coefficients[0].real, 2*coefficients[1:orders+1].real


def masked_probabilities(time, theta):
    edge_masks = masks()
    signs = np.array([(-1)**(4-sum(mask)) for mask in edge_masks])
    probabilities = np.stack([phase_scan(time, theta, mask=mask) for mask in edge_masks])
    return signs, probabilities


def wrap(phase):
    return (phase + pi) % (2*pi) - pi


def audit_square():
    """Independent matrix, spectral, finite-difference and DFT checks."""
    maximum = dict.fromkeys(("direct_expm", "gauge_invariance", "tree_invariance", "masked_identity"), 0.0)
    for angle in (0., 0.73, -0.73, pi/2, pi, 3*pi/2):
        for time in (0.11, 0.8, 1.2, 1.6):
            h = square(angle)
            p = spectral_return(h, time)
            maximum["direct_expm"] = max(
                maximum["direct_expm"], abs(p-direct_return(direct_square(angle), time)),
            )
            maximum["gauge_invariance"] = max(maximum["gauge_invariance"], abs(
                p-direct_return(rephase(h, [0.57, -0.31, 0.24, -0.88]), time),
            ))
        for mask in masks()[:-1]:
            maximum["tree_invariance"] = max(maximum["tree_invariance"], abs(
                spectral_return(square(angle, mask=mask), 1.6)-direct_return(direct_square(0, mask=mask), 1.6),
            ))
        signs, probabilities = masked_probabilities(1.6, angle)
        maximum["masked_identity"] = max(maximum["masked_identity"], abs(
            harmonic(signs @ probabilities)-harmonic(phase_scan(1.6, angle)),
        ))
    assert max(maximum.values()) < 1e-12
    (_, amplitudes) = cosine_coefficients(PRIMARY_TIME)
    np.testing.assert_allclose(amplitudes[:3], [-.255094, .039978, .000428], atol=8e-7, rtol=0)
    theta = PLANTED_PHASE
    probe = 0.31*np.cos(theta + OFFSETS) + 0.77*np.cos(2*(theta + OFFSETS))
    np.testing.assert_allclose(harmonic(probe), .31*np.exp(1j*theta), atol=1e-13, rtol=0)
    thirds = .08*np.cos(3*(theta + OFFSETS))
    np.testing.assert_allclose(harmonic(thirds), .08*np.exp(-3j*theta), atol=1e-13, rtol=0)
    raw = harmonic(phase_scan(PRIMARY_TIME, theta))
    reversed_ = harmonic(phase_scan(PRIMARY_TIME, -theta))
    np.testing.assert_allclose(reversed_, raw.conjugate(), atol=1e-13, rtol=0)
    product = expm(-0.4j * direct_square(0, energies=(0, 0, 0, 0)))[:, 0]
    gauge_copy = product * np.array([1, 1, 1, -1])
    concurrence = float(2*abs(np.linalg.det(gauge_copy.reshape(2, 2))))
    np.testing.assert_allclose(abs(product)**2, abs(gauge_copy)**2, atol=1e-13, rtol=0)
    np.testing.assert_allclose(concurrence, np.sin(.8)**2, atol=1e-13, rtol=0)
    return {
        "maximum_discrepancies": maximum, "primary_first_three_cosine_harmonics": amplitudes[:3].tolist(),
        "diagonal_gauge_concurrence_example": {"original": 0.0, "gauge_copy": concurrence},
    }


def aliasing(time, theta):
    _, a = cosine_coefficients(time, orders=32)
    target = a[0]*np.exp(1j*theta)
    result = {"first_harmonic": [float(target.real), float(target.imag)]}
    for n in (4, 8, 16, 64):
        sampled = harmonic(phase_scan(time, theta, offsets=np.arange(n)*2*pi/n))
        remainder = sum(abs(value) for k, value in enumerate(a, 1) if k > 1 and k % n in (1, n-1))
        result[str(n)] = {
            "harmonic": [float(sampled.real), float(sampled.imag)],
            "alias_error": float(abs(sampled-target)), "alias_amplitude_bound": float(remainder),
            "angular_bias_rad": float(wrap(np.angle(sampled/a[0])-theta)),
            "angular_bound_rad": float(np.arcsin(remainder/abs(a[0]))) if remainder < abs(a[0]) else None,
        }
    return result
