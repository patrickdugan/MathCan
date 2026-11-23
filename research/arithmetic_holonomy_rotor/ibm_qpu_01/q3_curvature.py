"""AHR-08 local face spectroscopy and AHR-09 cubical reconstruction."""

from itertools import combinations, pairwise
from math import ceil, pi, sqrt

import numpy as np
from scipy.linalg import expm

from exact_oracle import direct_return, harmonic, spectral_return, wrap
from hamiltonian import OFFSETS

EDGES = tuple(sorted((s, s | (1 << i)) for i in range(3) for s in range(8) if not s & (1 << i)))
FACES = tuple((i, j, layer) for i, j in combinations(range(3), 2) for layer in range(2))
TREE = {(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 6), (3, 7)}
CHORDS = tuple(edge for edge in EDGES if edge not in TREE)
PROBES = ((0, 1), (2, 6), (5, 7))
BIANCHI = np.array([-1, 1, 1, -1, -1, 1])
ENERGIES = np.array([sum(np.log(p) for i, p in enumerate((2, 3, 5)) if s & (1 << i)) for s in range(8)])


def incidence():
    d0 = np.zeros((12, 8), dtype=int)
    d1 = np.zeros((6, 12), dtype=int)
    for row, (low, high) in enumerate(EDGES):
        d0[row, low], d0[row, high] = -1, 1
    for row, (i, j, layer) in enumerate(FACES):
        fixed = 3-i-j
        low = layer << fixed
        corners = (low, low | 1 << i, low | 1 << i | 1 << j, low | 1 << j, low)
        for a, b in pairwise(corners):
            d1[row, EDGES.index(tuple(sorted((a, b))))] = 1 if a < b else -1
    return d0, d1


def addresses():
    """One forward probe per face, unique starting corner and orientation correction."""
    _, d1 = incidence()
    result = []
    for row, (i, j, layer) in enumerate(FACES):
        probe, = (edge for edge in PROBES if d1[row, EDGES.index(edge)])
        axis = (probe[0]^probe[1]).bit_length()-1
        other = j if axis == i else i
        start = probe[0] ^ (1 << other)
        result.append({
            "face": [i, j, layer], "edge": probe, "sign": int(d1[row, EDGES.index(probe)]), "start": start,
        })
    return result


def cube(angles, probe=None, delta=0., mask=None):
    h = np.diag(ENERGIES).astype(complex)
    masks = {} if mask is None else mask
    for edge, angle in zip(EDGES, angles, strict=True):
        if not masks.get(edge, True):
            continue
        lo, hi = edge
        value = np.exp(1j*(angle + (delta if probe == edge else 0.0)))
        h[hi, lo], h[lo, hi] = value, value.conjugate()
    return h


def face_probabilities(angles, address, time, offsets=OFFSETS, *, independent=False, mask=None):
    calculate = direct_return if independent else spectral_return
    return np.array([calculate(
        cube(angles, address["edge"], address["sign"]*delta, mask=mask), time, address["start"],
    ) for delta in offsets])


def face_circuit(angles, address, time, delta):
    """Qiskit local-probe circuit, with little-endian basis-state preparation."""
    from qiskit import QuantumCircuit

    circuit = QuantumCircuit(3)
    for bit in range(3):
        if address["start"] & (1 << bit):
            circuit.x(bit)
    h = cube(angles, address["edge"], address["sign"]*delta)
    circuit.unitary(expm(-1j*time*h), range(3))
    return circuit


def project(face_angles, covariance=None):
    """Local wrapped GLS projection onto the nearest Bianchi-compatible branch."""
    cov = np.eye(6) if covariance is None else np.asarray(covariance)
    direction = cov @ BIANCHI
    denominator = BIANCHI @ direction
    if denominator <= 0:
        raise ValueError("positive variance along the Bianchi row is required")
    bianchi = wrap(np.asarray(face_angles) @ BIANCHI)
    return wrap(np.asarray(face_angles) - bianchi[..., None]*(direction/denominator))


def chords(face_angles):
    _, d1 = incidence()
    matrix = d1[:, [EDGES.index(edge) for edge in CHORDS]]
    assert all(abs(round(np.linalg.det(np.delete(matrix, i, axis=0)))) == 1 for i in range(6))
    inverse = np.rint(np.linalg.inv(matrix[:5])).astype(int)
    return wrap(np.asarray(face_angles)[..., :5] @ inverse.T)


def _tree_gauge(angles):
    phases = {0: 0.0}
    while len(phases) < 8:
        for lo, hi in TREE:
            raw = angles[EDGES.index((lo, hi))]
            if lo in phases and hi not in phases:
                phases[hi] = phases[lo] - raw
            elif hi in phases and lo not in phases:
                phases[lo] = phases[hi] + raw
    return wrap(np.array([angles[EDGES.index((lo, hi))]+phases[hi]-phases[lo] for lo, hi in CHORDS]))


def _scheduled_draws(angles, cases, time, shots, rng, samples):
    probabilities = np.stack([face_probabilities(angles, case, time) for case in cases])
    draws = {}
    result = []
    for i, case in enumerate(cases):
        fields = []
        for q, delta in enumerate(OFFSETS):
            # Only the probe-free offset can share a circuit across different edges.
            key = (case["start"], case["edge"] if q else None, case["sign"]*delta)
            if key not in draws:
                draws[key] = rng.binomial(shots, probabilities[i, q], samples) / shots
            fields.append(draws[key])
        result.append(harmonic(np.stack(fields, axis=1)))
    return np.stack(result, axis=1), len(draws)


def run_q3(*, seed=20261123, time=.4, shots=2048, samples=2500):
    from qiskit.quantum_info import Statevector

    d0, d1 = incidence()
    ranks = [int(np.linalg.matrix_rank(matrix)) for matrix in (d0, d1, BIANCHI[None, :])]
    assert ranks == [7, 5, 1] and not np.any(d1 @ d0) and not np.any(BIANCHI @ d1)
    rng = np.random.default_rng(seed)
    angles = rng.uniform(-pi, pi, 12)
    truth = wrap(d1 @ angles)
    cases = addresses()
    # Independent path classification: each starting corner lies in exactly one face incident to the probe.
    for row, case in enumerate(cases):
        touching = [f for f, values in enumerate(d1) if values[EDGES.index(case["edge"])]
                    and any(case["start"] in EDGES[k] for k, value in enumerate(values) if value)]
        assert touching == [row]
    np.testing.assert_allclose(wrap(chords(truth)-_tree_gauge(angles)), 0, atol=1e-12, rtol=0)

    short = time/sqrt(2)
    long_q = np.array([6/time**4 * harmonic(face_probabilities(angles, case, time)) for case in cases])
    short_q = np.array([6/short**4 * harmonic(face_probabilities(angles, case, short)) for case in cases])
    improved = 2*short_q-long_q
    residuals = wrap(np.angle(improved)-truth)
    independent_error = max(float(np.max(abs(face_probabilities(angles, case, time) -
                                              face_probabilities(angles, case, time, independent=True))))
                            for case in cases)
    qiskit_error = max(
        abs(Statevector.from_instruction(face_circuit(angles, case, time, delta)).probabilities()[case["start"]]
            - spectral_return(cube(angles, case["edge"], case["sign"]*delta), time, case["start"]))
        for case in cases for delta in OFFSETS
    )
    assert independent_error < 1e-12
    assert qiskit_error < 1e-12

    # A wrong corner sees the other face incident to the same probe at leading order.
    face = 0
    correct_case = cases[face]
    other_face = next(index for index, case in enumerate(cases)
                      if index != face and case["edge"] == correct_case["edge"])
    wrong_case = {**cases[other_face], "sign": correct_case["sign"]}
    tiny = .04
    near = 6/tiny**4 * harmonic(face_probabilities(angles, correct_case, tiny))
    wrong = 6/tiny**4 * harmonic(face_probabilities(angles, wrong_case, tiny))
    assert abs(near-np.exp(1j*truth[face])) < .01
    assert abs(wrong-np.exp(1j*truth[face])) > .1
    other_sign = cases[other_face]["sign"]
    expected_wrong = np.exp(1j*(truth[other_face] if other_sign == correct_case["sign"] else -truth[other_face]))
    assert abs(wrong-expected_wrong) < .01

    # Removing a marked edge need not eliminate probe dependence on an intact cube.
    selected_edges = [edge for edge, value in zip(EDGES, d1[face], strict=True) if value]
    parity_scan = np.zeros(4)
    for m in range(16):
        mask = {edge: bool(m & (1 << i)) for i, edge in enumerate(selected_edges)}
        parity_scan += (-1)**(4-m.bit_count())*face_probabilities(angles, correct_case, 1.3, mask=mask)
    overlapping_cycle_gap = float(abs(harmonic(parity_scan)-harmonic(face_probabilities(angles, correct_case, 1.3))))
    assert overlapping_cycle_gap > 1e-4

    q_long, long_settings = _scheduled_draws(angles, cases, time, shots, rng, samples)
    q_short, short_settings = _scheduled_draws(angles, cases, short, shots, rng, samples)
    noisy_local = np.angle(q_long)
    noisy_richardson = np.angle(12*q_short/short**4 - 6*q_long/time**4)
    noise = rng.normal(0, .08, size=(20_000, 6))
    raw = wrap(truth+noise)
    fitted = project(raw)
    projection_ratio = float(np.mean(wrap(fitted-truth)**2)/np.mean(wrap(raw-truth)**2))
    assert abs(projection_ratio-5/6) < .02
    fitted_ideal = project(np.angle(improved))
    zero_branch = float(wrap(BIANCHI @ fitted_ideal))
    np.testing.assert_allclose(zero_branch, 0, atol=1e-12)
    reconstructed = chords(fitted_ideal)
    rebuilt_faces = d1[:, [EDGES.index(edge) for edge in CHORDS]] @ reconstructed
    chord_face_error = float(max(abs(wrap(rebuilt_faces-fitted_ideal))))
    assert chord_face_error < 1e-12
    lower_per_face = ceil(216 / (time**6 * (10*pi/180)**2))
    return {
        "status": "simulation only", "cochain_ranks": ranks, "time": time, "short_time": short,
        "edge_order": EDGES, "probe_edges": PROBES, "chord_order": CHORDS, "face_addresses": cases,
        "true_face_phases": truth.tolist(), "local_face_phases": np.angle(long_q).tolist(),
        "richardson_face_phases": np.angle(improved).tolist(), "richardson_bias_rad": residuals.tolist(),
        "projected_richardson_face_phases": fitted_ideal.tolist(), "projected_bianchi_residual_rad": zero_branch,
        "projected_chord_round_trip_face_error_rad": chord_face_error,
        "true_chord_phases": _tree_gauge(angles).tolist(), "reconstructed_chord_phases": reconstructed.tolist(),
        "independent_probabilities_max_error": independent_error,
        "qiskit_probabilities_max_error": float(qiskit_error),
        "wrong_corner_complex_error": float(abs(wrong-np.exp(1j*truth[face]))),
        "overlapping_cycle_failure_of_unicyclic_identity": overlapping_cycle_gap,
        "gaussian_projection_mse_ratio": projection_ratio,
        "shot_monte_carlo": {
            "replicates": samples, "shots_per_setting": shots,
            "raw_rmse_deg": float(np.degrees(np.sqrt(np.mean(wrap(noisy_local-truth)**2)))),
            "richardson_rmse_deg": float(np.degrees(np.sqrt(np.mean(wrap(noisy_richardson-truth)**2)))),
            "projected_richardson_rmse_deg": float(np.degrees(np.sqrt(np.mean(wrap(project(noisy_richardson)-truth)**2)))),
        },
        "schedule": {
            "single_time_simple": 24, "single_time_deduplicated": long_settings,
            "two_time_simple": 48, "two_time_deduplicated": long_settings+short_settings,
            "single_time_shots": long_settings*shots, "two_time_shots": (long_settings+short_settings)*shots,
            "shared_counts_couple_face_errors": True,
        },
        "planning": {
            "timing_assumption_per_shot_s": 0.00052,
            "job_overhead_allowance_s": 60,
            "single_time_nominal_s": 60+long_settings*shots*.00052,
            "two_time_nominal_s": 60+(long_settings+short_settings)*shots*.00052,
            "target_phase_sd_deg": 10,
            "leading_order_shots_for_target_per_face": lower_per_face,
            "leading_order_seconds_six_faces": 60+6*lower_per_face*.00052,
            "richardson_short_long_allocation_ratio": sqrt(32),
        },
    }
