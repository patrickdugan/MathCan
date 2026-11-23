"""Build immutable simulation receipts and a proposed, disabled IBM manifest."""
import argparse
from dataclasses import asdict
from hashlib import sha256
from importlib.metadata import version
import json
from math import ceil
from pathlib import Path

import numpy as np
from qiskit import qpy

from backend_snapshot import write_json
from bianchi_reconstruction import branch_audit
from circuit_synthesis import LIMITS, METHODS, SEED, compact_target, physical_archive
from controls import BRANCH_SEED, CENTER, TRAINING, coupled_faces, exact_controls, held_out
from fisher_design import (EVALUATION_SEED, FACE_JACOBIAN, LEVELS, NUISANCE_NAMES, REPLICATES,
                           allocate, fisher, fit_likelihood, fit_transfer, harmonic_summary,
                           likelihood_summary, mirror_reference, nuisance_templates, response)
from noise_benchmark import CalibratedAer, benchmark, historical_snapshot
from plaquette_estimator import probability, settings, short_time_audit
from provenance import BASE, q2_audit
from q3_hamiltonian import (EDGE_INDEX, ENERGIES, TREE, audit, chord_field, face_flux,
                            gauge_transform)
from time_optimizer import optimize, richardson_cases

PRECISION_GATE = {"max_face_rmse_deg": 12., "min_marginal_coverage": .90,
                  "min_joint_chord_coverage": .90, "min_converged_fraction": .98}
BUDGET_POLICY = {"fixed_overhead_s": 20, "safety_factor": 1.5, "minimum_cap_s": 60}
CANDIDATE_SHOTS = 4096
FAIR_TOTAL = 98304


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def trial_rng(arm, shots):
    return np.random.default_rng(np.random.SeedSequence([EVALUATION_SEED, arm, shots]))


def eligible(summary):
    return all(summary[key] <= limit for key, limit in LIMITS.items())


class Study:
    def __init__(self, snapshot, synthesis):
        self.snapshot = snapshot
        self.target = compact_target(snapshot)
        self.aer = CalibratedAer(snapshot)
        self.synthesis = synthesis

    def scan(self, chords, cases):
        field = chord_field(chords)
        return benchmark(field, cases, self.synthesis, self.target, self.snapshot, self.aer)[3]

    def train(self, cases, fixtures):
        ideal = np.array([response(c, cases)[0] for c in TRAINING])
        noisy = np.array([self.scan(c, cases) for c in TRAINING])
        held = np.array([self.scan(c, cases) for c in fixtures])
        shared = nuisance_templates(CENTER, cases, noisy[0], .01)
        return fit_transfer(ideal, noisy, shared), noisy, held

    def likelihood_design(self, time, fixtures, repetitions):
        cases = settings([time])
        calibrated, training, fixture_p = self.train(cases, fixtures)
        p, jac = response(CENTER, cases)
        nominal = calibrated.map(p)
        derivative = np.column_stack((jac * calibrated.contrast[:, None], calibrated.shared))
        n_nuisance = calibrated.shared.shape[-1]
        labels = [(f"equal_{n}", np.full(len(cases), n)) for n in LEVELS]
        labels.append(("fisher_equal_total", allocate(nominal, derivative, FAIR_TOTAL, n_nuisance)))
        result = {}
        for label, shots in labels:
            arm = trial_rng(72, int(shots.sum()))
            indices = np.arange(repetitions) % len(fixtures)
            shared = arm.normal(size=(repetitions, len(NUISANCE_NAMES)))
            mean = np.clip(fixture_p[indices] + shared @ calibrated.nuisance.T, .002, .998)
            counts = arm.binomial(shots, mean)
            estimates, cov, converged = fit_likelihood(
                counts, shots, cases, calibrated, CENTER, iterations=8)
            summary = likelihood_summary(estimates, cov, fixtures[indices], converged)
            ideal_fisher = fisher(nominal, derivative, shots, n_nuisance)
            local_cov = np.linalg.inv(ideal_fisher)[:5, :5]
            face_cov = FACE_JACOBIAN @ local_cov @ FACE_JACOBIAN.T
            result[label] = {"replicates": repetitions, "shots_per_case": shots.tolist(),
                             "total_shots": int(shots.sum()), "nominal_face_effective_info_rad-2":
                             (1/np.diag(face_cov)).tolist(),
                             "nominal_chord_cov_rad2": local_cov.tolist(), **summary}
            if label == f"equal_{CANDIDATE_SHOTS}":
                # Twice the assumed drift/readout/coupling scales. Same field set.
                extreme = np.clip(fixture_p[indices] + 2*shared @ calibrated.nuisance.T, .002, .998)
                estimates, cov, converged = fit_likelihood(arm.binomial(shots, extreme), shots,
                                                           cases, calibrated, CENTER, iterations=8)
                result["double_shared_drift_stress"] = likelihood_summary(
                    estimates, cov, fixtures[indices], converged)
        return {"time": time, "evaluations": result, "transfer_train_cases": len(training),
                "transfer_intercept": calibrated.intercept.tolist(),
                "transfer_contrast": calibrated.contrast.tolist(),
                "heldout_transfer_abs_error_max": float(np.max(abs(
                    fixture_p - calibrated.map(np.array([response(c, cases)[0] for c in fixtures]))))),
                "nominal_shared_covariance_rad_free_p": (
                    calibrated.shared @ calibrated.shared.T).tolist()}

    def fourier_design(self, label, time, count, fixtures, repetitions):
        richardson = label == "richardson"
        cases = richardson_cases(time) if richardson else settings([time], count)
        n = len(cases)
        reference = self.scan(np.zeros(5), cases)
        fixture_p = np.array([self.scan(f, cases) for f in fixtures])
        target_modes = nuisance_templates(CENTER, cases, self.scan(CENTER, cases), .01)
        reference_modes = nuisance_templates(np.zeros(5), cases, reference, .01)
        strategies = [(f"equal_{shots}", np.arange(n), None, shots) for shots in LEVELS]
        strategies += [("equal_total", np.arange(n), FAIR_TOTAL, None)]
        if label == "four":
            strategies += [("shared_reference_equal_total", mirror_reference(cases), FAIR_TOTAL, None)]
        result = {}
        for name, groups, total, uniform in strategies:
            flight = np.array([np.flatnonzero(groups == k)[0] for k in range(max(groups)+1)])
            width = n + len(flight)
            if total is None:
                shots = np.full(width, uniform)
            else:
                shots = np.full(width, total//width)
                shots[:total % width] += 1
            points = np.arange(repetitions) % len(fixtures)
            nominal = np.column_stack((fixture_p[points], np.broadcast_to(reference[flight],
                                                                         (repetitions, len(flight)))))
            shared = np.vstack((target_modes, reference_modes[flight]))
            arm = trial_rng(11 + count + 30 * richardson, int(shots.sum()))
            means = np.clip(nominal + arm.normal(size=(repetitions, len(NUISANCE_NAMES))) @ shared.T,
                            .002, .998)
            samples = arm.binomial(shots, means) / shots
            record = harmonic_summary(samples, shots, shared, fixtures[points],
                                      count, groups, richardson)
            result[name] = {"replicates": repetitions, "shots_per_case": shots.tolist(),
                            "total_shots": int(shots.sum()), "reference_circuits": len(flight),
                            "fisher_effective_per_face_rad-2": (
                                (1.959964 / np.radians(record["median_face_halfwidth_deg"]))**2).tolist(),
                            **record}
        return {"time": time, "offsets": count, "evaluations": result,
                "shared_ref_max_expected_probability_mismatch": float(max(abs(
                    reference - reference[np.array([np.flatnonzero(mirror_reference(cases) == k)[0]
                                                    for k in mirror_reference(cases)])])))}

    def controls_and_manifest(self, time, account, statistics, out):
        cases = settings([time])
        tree = np.zeros(12)
        tree[[EDGE_INDEX[edge] for edge in TREE]] = 1.
        copy = gauge_transform(chord_field(CENTER), np.random.default_rng(6135).normal(size=8))
        detuning = ENERGIES + .12*np.array([0, 1, -1, 0, 1, 2, 0, 1])
        specifications = [
            ("signal", chord_field(CENTER), cases, 1., ENERGIES),
            ("zero", np.zeros(12), cases[:4], 1., ENERGIES),
            ("reverse", chord_field(-CENTER), cases[:4], 1., ENERGIES),
            ("tree", chord_field(CENTER), cases[:4], tree, ENERGIES),
            ("gauge_copy", copy, cases[:4], 1., ENERGIES),
            ("detuned", chord_field(CENTER), cases[:4], 1., detuning),
            ("balanced_excitation", coupled_faces(), cases[:4], 1., ENERGIES),
        ]
        packs, audits = [], {}
        for role, field, arm, weight, energy in specifications:
            summary, circuits, _, p = benchmark(field, arm, self.synthesis, self.target, self.snapshot,
                                                 self.aer, weight, energy, keep_details=True)
            from plaquette_estimator import harmonic
            z = harmonic(p.reshape(-1, 4))
            audits[role] = {"exact_z_re_im": np.column_stack((
                harmonic(probability(field, arm, weight, energy).reshape(-1, 4)).real,
                harmonic(probability(field, arm, weight, energy).reshape(-1, 4)).imag)).tolist(),
                "aer_z_re_im": np.column_stack((z.real, z.imag)).tolist(),
                "circuit_summary": {k: v for k, v in summary.items() if k != "per_setting"}}
            rows = []
            for case, circuit, row in zip(arm, circuits, summary["per_setting"]):
                case_id = f"{role}/{case.id}"
                circuit.metadata["case_id"] = case_id
                circuit.metadata["role"] = role
                rows.append((physical_archive(circuit, self.snapshot),
                             {**row, "case_id": case_id, "role": role, "shots": CANDIDATE_SHOTS,
                              "setting": asdict(case)}))
            packs.append(rows)
        # Interleave available controls early. The lone target arm then fills out
        # all six face measurements in its own registered ordering.
        packed = [p[i] for i in range(max(map(len, packs))) for p in packs if i < len(p)]
        circuits, rows = map(list, zip(*packed))
        assert len({r["case_id"] for r in rows}) == len(rows)
        qpy_path = out / "q3_candidate_isa.qpy"
        with qpy_path.open("wb") as stream:
            qpy.dump(circuits, stream)
        rep_delay = self.snapshot["rep_delay_s"]
        # IBM normally uses 250us. Missing backend default is an explicit HOLD
        # even though a conservative indicative estimate can still be archived.
        budget_delay = rep_delay if rep_delay is not None else .00025
        duration = sum(r["shots"]*(r["critical_path_s"] + budget_delay) for r in rows)
        nominal = duration + BUDGET_POLICY["fixed_overhead_s"]
        cap = max(BUDGET_POLICY["minimum_cap_s"], ceil(nominal*BUDGET_POLICY["safety_factor"]))
        info = statistics["evaluations"][f"equal_{CANDIDATE_SHOTS}"]
        statistical_checks = {
            "precision": info["max_face_rmse_deg"] <= PRECISION_GATE["max_face_rmse_deg"],
            "marginal_coverage": min(info["face_coverage_95"]) >= PRECISION_GATE["min_marginal_coverage"],
            "joint_coverage": info["joint_chord_coverage_95"] >= PRECISION_GATE["min_joint_chord_coverage"],
            "convergence": info["converged_fraction"] >= PRECISION_GATE["min_converged_fraction"],
            "full_replicates": info["replicates"] >= REPLICATES,
        }
        reasons = [name for name, passed in statistical_checks.items() if not passed]
        if account is None:
            reasons.append("current Open Plan balance and live physical calibration unverified")
        elif cap > account["remaining_qpu_seconds"]:
            reasons.append("provisional cap exceeds verified free seconds")
        if rep_delay is None:
            reasons.append("backend repetition delay not verified")
        if any(not eligible(a["circuit_summary"]) for a in audits.values()):
            reasons.append("candidate circuits fail registered compilation limits")
        calibration_digest = sha256((out / "calibration.json").read_bytes()).hexdigest()
        charter = {"design_decision": "HOLD" if reasons else "GO design only",
                   "execution_decision": "HOLD pending separate exact manifest approval",
                   "qpu_submitted": False, "approval_granted": False, "hardware_launcher_included": False,
                   "hold_reasons": reasons, "prespecified_statistical_checks": statistical_checks,
                   "calibration_timestamp": self.snapshot["calibration_timestamp"],
                   "calibration_sha256": calibration_digest,
                   "qpy_sha256": sha256(qpy_path.read_bytes()).hexdigest(),
                   "backend": self.snapshot["backend"], "backend_width": self.snapshot["backend_width"],
                   "physical_xyz": self.snapshot["selection"]["physical_xyz"], "transpiler_seed": SEED,
                   "q2_archived_balance_seconds": 515, "current_verified_open_plan": account,
                   "synthesis": self.synthesis, "likelihood_time": time,
                   "circuits": len(circuits), "total_shots": sum(r["shots"] for r in rows),
                   "timing_estimate_s": duration, "nominal_qpu_usage_s": nominal,
                   "provisional_max_execution_time_s": cap, "backend_rep_delay_s": rep_delay,
                   "budget_policy": BUDGET_POLICY,
                   "expected_primary_faces_deg": np.degrees(face_flux(chord_field(CENTER))).tolist(),
                   "simulated_median_marginal_95_halfwidth_deg": info["median_face_halfwidth_deg"],
                   "settings": rows, "simulation_only_controls": audits}
        return charter


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--snapshot", type=Path, help="A provenance-labeled snapshot or read-only inventory")
    parser.add_argument("--grid-cache", type=Path, help="save or reuse the same calibration's training grid")
    parser.add_argument("--quick", action="store_true", help="reduced smoke test, never eligible for GO")
    args = parser.parse_args()
    out = args.out
    out.mkdir(parents=True, exist_ok=True)
    calibration = read(args.snapshot) if args.snapshot else historical_snapshot()
    write_json(out / "calibration.json", calibration)
    snapshot = calibration["backend"]
    receipt = {"source": q2_audit(), "integer_algebra": audit(),
               "short_time": short_time_audit(chord_field(CENTER), 1.1+np.arange(12)/50),
               "mathcan_base": BASE, "transpiler_seed": SEED,
               "software": {p: version(p) for p in
                            ("numpy", "scipy", "qiskit", "qiskit-aer", "qiskit-ibm-runtime")},
               "compilation_limits": LIMITS, "statistical_limits": PRECISION_GATE,
               "training_chord_configurations": TRAINING.tolist(),
               "nuisance_names": NUISANCE_NAMES, "evaluation_seed": EVALUATION_SEED}
    write_json(out / "provenance.json", receipt)
    probe = Study(snapshot, "exact")
    bakeoff_cases = settings([.6, 1.1, 1.6])
    if args.quick:
        bakeoff_cases = settings([.8])[::4]
    methods = METHODS if not args.quick else ("exact", "exact-sabre3", "edge-2")
    comparison = {}
    for method in methods:
        summary, *_ = benchmark(chord_field(CENTER), bakeoff_cases, method, probe.target,
                                snapshot, probe.aer, keep_details=True)
        comparison[method] = {"eligible": eligible(summary), **summary}
        print("Compiled", method, summary["max_two_qubit_gates"], flush=True)
    write_json(out / "compilation.json", comparison)
    synthesis = min((m for m in comparison if comparison[m]["eligible"]),
                    key=lambda m: comparison[m]["total_two_qubit_gates"])
    study = Study(snapshot, synthesis)
    cache_key = sha256(json.dumps({"snapshot": snapshot, "method": synthesis},
                                  sort_keys=True).encode()).hexdigest()
    if args.quick:
        grid = {"selection": {"4": 1.1, "8": 1.1, "likelihood": 1.1, "richardson": 1.1}}
    elif args.grid_cache and args.grid_cache.exists():
        cached = read(args.grid_cache)
        if cached["key"] != cache_key:
            raise ValueError("training-grid cache is for another calibration or synthesis")
        grid = cached["grid"]
    else:
        grid = optimize(synthesis, study.target, snapshot, study.aer)
        if args.grid_cache:
            write_json(args.grid_cache, {"key": cache_key, "grid": grid})
    write_json(out / "time_grid.json", grid)
    t = grid["selection"]
    print("Registered training choices", t, flush=True)
    fixtures = held_out()
    repetitions = 12 if args.quick else REPLICATES
    statistics = {}
    for label, time, count in (("four", t["4"], 4), ("eight", t["8"], 8),
                               ("richardson", t["richardson"], 4)):
        statistics[label] = study.fourier_design(label, time, count, fixtures, repetitions)
        print("Evaluated", label, flush=True)
    statistics["likelihood"] = study.likelihood_design(t["likelihood"], fixtures, repetitions)
    write_json(out / "statistics.json", {"repetitions_per_design": repetitions,
                                        "heldout_chords": fixtures.tolist(), "designs": statistics})
    write_json(out / "controls.json", {"exact": exact_controls(t["likelihood"]),
                                      "branch": branch_audit(np.random.default_rng(BRANCH_SEED))})
    manifest = study.controls_and_manifest(t["likelihood"], calibration["account"],
                                           statistics["likelihood"], out)
    write_json(out / "q3_candidate_manifest.json", manifest)
    print("Decision", manifest["design_decision"], manifest["hold_reasons"], flush=True)


if __name__ == "__main__":
    main()
