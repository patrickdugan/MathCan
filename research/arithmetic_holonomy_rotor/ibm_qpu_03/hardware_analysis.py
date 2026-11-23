"""Replay the Q3 return-count analysis against the frozen calibrated model."""
import argparse
from pathlib import Path

import numpy as np
from scipy.stats import chi2, norm

from backend_snapshot import write_json
from controls import CENTER
from fisher_design import Calibration, FACE_JACOBIAN, fit_likelihood
from plaquette_estimator import harmonic, settings
from q3_hamiltonian import BIANCHI, chord_field, face_flux, wrap
from run_study import read


def wilson(successes, shots, z=1.959963984540054):
    p = np.asarray(successes, dtype=float) / shots
    denominator = 1 + z**2 / shots
    center = (p + z**2 / (2 * shots)) / denominator
    radius = z * np.sqrt(p * (1 - p) / shots + z**2 / (4 * shots**2)) / denominator
    return center - radius, center + radius


def complex_parts(z):
    return [float(z.real), float(z.imag)]


def quadrature_record(rows):
    successes = np.array([r["return_count"] for r in rows])
    shots = np.array([r["shots"] for r in rows])
    p = successes / shots
    lower, upper = wilson(successes, shots, norm.ppf(1 - .05 / 8))
    real = [(lower[0] - upper[2]) / 2, (upper[0] - lower[2]) / 2]
    imag = [(lower[3] - upper[1]) / 2, (upper[3] - lower[1]) / 2]
    return {"observed_re_im": complex_parts(harmonic(p)),
            "exact_re_im": complex_parts(harmonic([r["exact"] for r in rows])),
            "aer_re_im": complex_parts(harmonic([r["aer"] for r in rows])),
            "simultaneous_95_counting_rectangle": [real, imag],
            "counting_rectangle_contains_origin": bool(real[0] <= 0 <= real[1] and imag[0] <= 0 <= imag[1])}


def analyze(manifest, hardware, likelihood, execution, boundaries=None):
    case_ids = [r["case_id"] for r in manifest["settings"]]
    assert list(hardware["counts"]) == case_ids
    assert len(set(case_ids)) == 48
    rows, groups = [], {}
    for case in manifest["settings"]:
        count = hardware["counts"][case["case_id"]]
        shots = case["shots"]
        assert sum(count.values()) == shots == 4096
        outcome = format(case["setting"]["start"], "03b")
        returns = count.get(outcome, 0)
        low, high = wilson(returns, shots)
        row = {**case, "return_outcome": outcome, "return_count": returns,
               "observed": returns / shots, "wilson_95": [float(low), float(high)]}
        rows.append(row)
        groups.setdefault((row["role"], row["setting"]["face"]), []).append(row)
    for group in groups.values():
        group.sort(key=lambda row: row["setting"]["offset_index"])
        assert [row["setting"]["offset_index"] for row in group] == [0, 1, 2, 3]
    primary = [row for face in range(6) for row in groups["signal", face]]
    cases = settings([manifest["likelihood_time"]])
    assert [r["case_id"] for r in primary] == [f"signal/{c.id}" for c in cases]
    correlation = np.asarray(likelihood["nominal_shared_covariance_rad_free_p"])
    variances, modes = np.linalg.eigh(correlation)
    kept = variances > 1e-15
    shared = modes[:, kept] * np.sqrt(variances[kept])
    transfer = Calibration(np.asarray(likelihood["transfer_intercept"]),
                           np.asarray(likelihood["transfer_contrast"]), shared,
                           np.empty((len(cases), 0)))
    counts = np.array([r["return_count"] for r in primary])
    shots = np.array([r["shots"] for r in primary])
    estimates, covariances, converged = fit_likelihood(
        counts[None, :], shots, cases, transfer, CENTER, iterations=24)
    chords, covariance = estimates[0], covariances[0]
    faces = face_flux(chord_field(chords))
    expected_faces = face_flux(chord_field(CENTER))
    face_covariance = FACE_JACOBIAN @ covariance @ FACE_JACOBIAN.T
    chord_offset = wrap(chords - CENTER)
    chisq = float(chord_offset @ np.linalg.solve(covariance, chord_offset))
    phase = {
        "fit_converged": bool(converged[0]), "estimated_faces_deg": np.degrees(faces).tolist(),
        "expected_faces_deg": np.degrees(expected_faces).tolist(),
        "face_errors_deg": np.degrees(wrap(faces - expected_faces)).tolist(),
        "face_local_95_halfwidth_deg": np.degrees(1.96 * np.sqrt(np.diag(face_covariance))).tolist(),
        "estimated_chords_deg": np.degrees(chords).tolist(),
        "expected_chords_deg": np.degrees(CENTER).tolist(),
        "chord_local_95_halfwidth_deg": np.degrees(1.96 * np.sqrt(np.diag(covariance))).tolist(),
        "expected_field_in_local_joint_95_region": bool(chisq <= chi2.ppf(.95, 5)),
        "expected_field_local_joint_chi_square": chisq,
        "wrapped_bianchi_closure_deg": float(np.degrees(wrap(BIANCHI @ faces))),
        "closure_enforced_by_fit": True,
    }
    quadratures = {f"{role}/f{face}": quadrature_record(group)
                   for (role, face), group in groups.items()}
    signal = groups["signal", 0]
    copy = groups["gauge_copy", 0]
    gauge_check = [b["observed"] - a["observed"] for a, b in zip(signal, copy, strict=True)]
    comparison = {}
    for model in ("exact", "compiled", "aer"):
        difference = np.array([r["observed"] - r[model] for r in primary])
        comparison[model] = {"return_rmse": float(np.sqrt(np.mean(difference**2))),
                             "max_abs_return_error": float(np.max(abs(difference)))}
    endpoint = execution.get("calibration_at_last_chunk") or execution.get("calibration_at_completion")
    timestamps = [execution.get("calibration_at_job_start"), endpoint]
    if boundaries:
        assert boundaries["job_id"] == execution["job_id"] == hardware["job_id"]
    return {"job_id": hardware["job_id"], "shots": sum(r["shots"] for r in rows),
            "pub_case_ids_match": hardware["pub_case_ids_match"],
            "execution_calibration_timestamps_match_preflight": all(
                bool(ts) and ts == execution["calibration_preflight"] for ts in timestamps),
            "selected_numeric_boundary_calibrations_equal":
            boundaries["selected_numeric_calibration_equal"] if boundaries else None,
            "likelihood": phase, "primary_return_error": comparison,
            "gauge_copy_minus_signal_return": gauge_check,
            "quadratures": quadratures, "cases": rows}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest", type=Path, required=True)
    p.add_argument("--statistics", type=Path, required=True)
    p.add_argument("--hardware", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    stats = read(args.statistics)["designs"]["likelihood"]
    boundaries = args.hardware / "boundary_calibration.json"
    report = analyze(read(args.manifest), read(args.hardware / "hardware_counts.json"), stats,
                     read(args.hardware / "execution_evidence.json"),
                     read(boundaries) if boundaries.exists() else None)
    write_json(args.output, report)


if __name__ == "__main__":
    main()
