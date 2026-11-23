from pathlib import Path

import numpy as np
import pytest
from qiskit import QuantumCircuit
from qiskit.quantum_info import SparsePauliOp

from circuit_synthesis import benchmark, compact_target, embed, measurements
from exact_oracle import (
    aliasing,
    audit_square,
    direct_square,
    harmonic,
    phase_scan,
    wrap,
)
from experiment import Hold, calibration_digest, digest, load, submission
from hamiltonian import (
    PLANTED_PHASE,
    PRIMARY_TIME,
    REFERENCE_OFFSET,
    pilot,
    square_paulis,
)
from hardware_analysis import summarize
from noise_benchmark import benchmark_noise
from phase_estimator import acceptance, estimate, fisher, rectangle, shot_benchmark
from q3_curvature import BIANCHI, addresses, chords, incidence, project, run_q3

ROOT = Path(__file__).resolve().parents[1]


def test_independent_square_and_aliases():
    audit = audit_square()
    assert max(audit["maximum_discrepancies"].values()) < 1e-12
    result = aliasing(PRIMARY_TIME, PLANTED_PHASE + REFERENCE_OFFSET)
    assert result["4"]["alias_error"] < result["4"]["alias_amplitude_bound"] < .001
    assert result["8"]["alias_error"] < result["4"]["alias_error"]


def test_little_endian_y_edge_and_reverse():
    for case in pilot():
        a = direct_square(case.phase, case.energy, case.mask)
        b = SparsePauliOp.from_list(square_paulis(case.phase, case.energy, case.mask)).to_matrix()
        np.testing.assert_allclose(a, b, atol=1e-12, rtol=0)
    assert direct_square(np.pi/2)[3, 1].imag == 1
    assert direct_square(-np.pi/2)[3, 1].imag == -1
    assert len(pilot()) == len({case.id for case in pilot()}) == 36


def test_calibration_recovers_both_signs_and_short_time_reference():
    for time in (0.8, 1.6):
        for theta in (-PLANTED_PHASE, PLANTED_PHASE):
            n = 8192
            signal = np.rint(n*phase_scan(time, theta+REFERENCE_OFFSET)).astype(int)
            reference = np.rint(n*phase_scan(time, REFERENCE_OFFSET)).astype(int)
            result = estimate(signal, reference, n)
            assert abs(wrap(result["relative_phase_rad"]-theta)) < .008
            assert result["phase_identifiable_at_95"]
    dark = estimate([50]*4, [51]*4, 100)
    assert dark["relative_phase_rad"] is None
    assert not dark["phase_identifiable_at_95"]


def test_intervals_and_acceptance():
    assert rectangle([0, 8, 0, 8], 8)["probability_intervals"][0][0] == 0
    p = np.array([.35, .12, .28, .4])
    shots = 8192
    counts = np.rint(shots*p).astype(int)
    assert acceptance(counts, shots, harmonic(p), [p])["passes"]
    unexpected = np.rint(shots*(p + [0, 0, 0, .20])).astype(int)
    assert not acceptance(unexpected, shots, harmonic(p), [p])["passes"]


def test_matched_total_budget_and_fisher():
    time = 1.6
    a = phase_scan(time, PLANTED_PHASE+REFERENCE_OFFSET)
    b = phase_scan(time, REFERENCE_OFFSET)
    trials = shot_benchmark(time, {"intact": (a, b)})
    for shots, row in trials.items():
        assert 128*row["exhaustive_shots_per_setting"] == row["total_shots_both_arms_each_protocol"]
        assert 8*int(shots) == row["total_shots_both_arms_each_protocol"]
        assert row["exhaustive_ideal_equal_total"]["angular_rmse_deg"] > row["intact"]["angular_rmse_deg"]
    bound = fisher(time)
    assert bound["estimated_reference_cr_sd_deg"] > bound["known_reference_cr_sd_deg"]


def test_cube_face_addresses_and_tree_inverse():
    assert len({tuple(row["edge"]) for row in addresses()}) == 3
    _, d1 = incidence()
    assert not np.any(BIANCHI @ d1)
    phases = d1 @ np.arange(12)/4
    corrected = project(phases+.03*BIANCHI)
    np.testing.assert_allclose(wrap(corrected-phases), 0, atol=1e-12)
    assert chords(corrected).shape == (5,)
    receipt = run_q3()
    assert receipt["qiskit_probabilities_max_error"] < 1e-12
    assert receipt["schedule"]["single_time_deduplicated"] == 23


def test_calibrated_compiled_q2_subset():
    snapshot = load(ROOT / "receipts/calibration.json")
    cases = pilot()[:4] + [case for case in pilot() if case.arm == "signal" and case.time == 1.6]
    # The benchmark requires a complete primary signal scan; discard any overlap.
    unique = list({case.id: case for case in cases}.values())
    chosen, circuits, metrics, _ = benchmark(unique, snapshot)
    assert metrics[chosen]["eligible"] and compact_target(snapshot).num_qubits == 2
    assert all(measurements(embed(c, snapshot)) == tuple(snapshot["physical_pair_xy"]) for c in circuits)
    noise = benchmark_noise(circuits[:1], snapshot)
    assert all(0 <= probs[0] <= 1 for probs in noise.values())


def test_readout_order_and_explicit_hardware_gate(tmp_path):
    circuit = QuantumCircuit(2)
    circuit.x(0)
    snapshot = {"compact_noise_model": {"errors": [
        {"type": "roerror", "operations": ["measure"], "gate_qubits": [[0]],
         "probabilities": [[0., 1.], [1., 0.]]},
    ]}}
    probabilities = benchmark_noise([circuit], snapshot)
    assert abs(probabilities["calibrated_aer"][0] - 1) < 1e-12
    assert abs(probabilities["readout_off"][0]) < 1e-12
    with pytest.raises(Hold, match="separate approval"):
        submission(None, tmp_path, 2048, authorized=False)


def test_hardware_analysis_keeps_phases_and_tree_separate():
    cases = pilot()
    counts = {}
    exact = {}
    for case in cases:
        name = f"{case.arm}_t{case.time:.1f}"
        probabilities = phase_scan(
            case.time, case.theta + case.reference_offset, energies=case.energy, mask=case.mask,
        )
        exact[name] = probabilities
        zeros = round(2048*probabilities[case.quadrant])
        counts[case.id] = {"00": zeros, "01": 2048-zeros}
    manifest = {
        "case_order": [case.id for case in cases], "cases": [case.record() for case in cases],
        "primary": {"signal": "signal_t1.6"},
    }
    hardware = {"counts": counts, "job_id": "local-test", "shots_per_circuit": 2048}
    rows = summarize(manifest, {"exact": exact, "calibrated_aer": exact}, hardware)
    groups = rows["four_phase_groups"]
    assert rows["primary_acceptance"]["passes"] and rows["tree_rectangle_contains_origin"]
    assert groups["signal_t1.6"]["reference_calibrated_phase"]["relative_phase_rad"] > 0
    assert groups["reversed_t1.6"]["reference_calibrated_phase"]["relative_phase_rad"] < 0
    assert "reference_calibrated_phase" not in groups["matched_detuning_t1.6"]


def test_calibration_digest_survives_git_line_ending_conversion(tmp_path):
    snapshot = tmp_path / "calibration.json"
    snapshot.write_bytes(b'{\r\n  "sample": 1\r\n}\r\n')
    normalized = calibration_digest(snapshot)
    assert normalized != digest(snapshot)
    snapshot.write_bytes(snapshot.read_bytes().replace(b"\r\n", b"\n"))
    assert calibration_digest(snapshot) == digest(snapshot) == normalized
