"""Cross-check small signals, consistent face excitations and confounding loops."""
from dataclasses import replace

import numpy as np

from plaquette_estimator import harmonic, probability, settings
from q3_hamiltonian import (BIANCHI, EDGE_INDEX, ENERGIES, TREE, chord_field, face_flux,
                            gauge_transform, matrix, phases_from_faces, wrap)

CENTER = np.array([.32, -.36, .28, -.31, .53])
TRAINING = np.array([CENTER, np.zeros(5), .55 * CENTER, -.45 * CENTER,
                     CENTER + np.array([-.18, .08, .13, .15, -.1])])
HELD_OUT_FIELD_SEED = 903017
BRANCH_SEED = 903019


def held_out(count=5):
    rng = np.random.default_rng(HELD_OUT_FIELD_SEED)
    return CENTER + rng.uniform(-.19, .19, size=(count, 5))


def coupled_faces(phase=.61):
    # Excite one independent face. A second oriented face balances its flux.
    faces = np.zeros(6)
    faces[[0, 5]] = phase
    assert BIANCHI @ faces == 0
    return chord_field(phases_from_faces(faces))


def exact_controls(time):
    field = chord_field(CENTER)
    cases = settings([time], 8)
    p = probability(field, cases)
    transform = np.random.default_rng(6135).normal(size=8)
    transformed = gauge_transform(field, transform)
    diagonal = np.diag(np.exp(1j * transform))
    np.testing.assert_allclose(matrix(transformed), diagonal @ matrix(field) @ diagonal.conj().T,
                               atol=2e-14)
    gauge = max(abs(p - probability(transformed, cases)))
    reverse = probability(-field, cases).reshape(6, 8)
    conjugate = np.conj(harmonic(p.reshape(6, 8)))
    reversal = max(abs(harmonic(reverse) - conjugate))
    zero = harmonic(probability(np.zeros(12), cases).reshape(6, 8))
    tree = np.zeros(12)
    tree[[EDGE_INDEX[e] for e in TREE]] = 1
    tree_scan = probability(field, cases, tree).reshape(6, 8)
    detuning = ENERGIES + .12 * np.array([0, 1, -1, 0, 1, 2, 0, 1])
    detuned = probability(field, cases, energies=detuning)
    detuned_copy = probability(transformed, cases, energies=detuning)
    wrong = [replace(c, start=0) for c in settings([.06], 8)[:8]]
    right_a = settings([.06], 8)[:8]
    # For the edge (0,1), the two incident face orientations both traverse
    # positively. Probe the other away corner with the same edge.
    right_b = [replace(c, start=4) for c in right_a]
    wrong_h = harmonic(probability(field, wrong)) * 6 / .06**4
    summed = (harmonic(probability(field, right_a)) + harmonic(probability(field, right_b))) * 6 / .06**4
    assert abs(wrong_h - summed) < .05
    assert gauge < 2e-14 and reversal < 2e-14
    assert np.max(np.ptp(tree_scan, axis=-1)) < 2e-14
    assert np.max(abs(zero.imag)) < 2e-14
    assert max(abs(detuned - detuned_copy)) < 2e-14
    excitation = face_flux(coupled_faces())
    np.testing.assert_allclose(excitation, [0.61, 0, 0, 0, 0, .61], atol=1e-15)
    return {"gauge_copy_max_spread": float(gauge), "reversal_conjugacy_error": float(reversal),
            "tree_flux_spread": float(np.max(np.ptp(tree_scan, axis=-1))),
            "zero_harmonic_real": zero.real.tolist(), "zero_harmonic_imag": zero.imag.tolist(),
            "detuning_effect_max": float(max(abs(detuned - p))),
            "detuned_gauge_copy_max_spread": float(max(abs(detuned - detuned_copy))),
            "compatible_excitation_face_angles": wrap(excitation).tolist(),
            "wrong_corner_short_time_complex": [wrong_h.real, wrong_h.imag],
            "two_incident_squares_short_time_complex": [summed.real, summed.imag]}
