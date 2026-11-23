"""AHR-QPU-01 reproducible simulation, preparation and explicitly gated hardware CLI."""

import argparse
import csv
import hashlib
import json
import logging
import os
from math import ceil
from pathlib import Path
from uuid import uuid4

import numpy as np
from qiskit import qpy
from qiskit.exceptions import QiskitError
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
from qiskit_ibm_runtime.api.exceptions import RequestsApiError
from requests.exceptions import RequestException

from circuit_synthesis import SEED, benchmark, capture, embed, grouped, now
from exact_oracle import aliasing, audit_square, harmonic
from hamiltonian import (
    ORDER_SEED,
    PLANTED_PHASE,
    PRIMARY_TIME,
    REFERENCE_OFFSET,
    TIMES,
    pilot,
)
from noise_benchmark import benchmark_noise
from phase_estimator import (
    REPLICATES,
    SYSTEMATIC_FLOOR,
    acceptance,
    complex_record,
    estimate,
    fisher,
    shot_benchmark,
)
from phase_estimator import SEED as MC_SEED
from q3_curvature import run_q3

ROOT = Path(__file__).resolve().parent
SHOT_LEVELS = (2048, 8192)
PROTOCOL = "ahr-qpu-01"


class Hold(RuntimeError):
    """A runtime condition did not pass the free-QPU gate."""


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write(path, value):
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(value, indent=2, allow_nan=False)+"\n", encoding="utf-8")
    temp.replace(path)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def budget(rows, shots):
    missing = sorted({gate for row in rows for gate in row["unknown_duration_gates"]})
    active = shots*sum(.0005 + row["serial_duration_s"] for row in rows)
    return {"circuits": len(rows), "shots_per_circuit": shots, "shots_total": len(rows)*shots,
            "serial_gate_measure_reset_allowance_s": active, "overhead_allowance_s": 60,
            "required_free_qpu_seconds": ceil(active+60), "unknown_instruction_durations": missing}


def simulate(snapshot_path, out):
    out.mkdir(parents=True, exist_ok=True)
    snapshot = load(snapshot_path)
    checks = audit_square()
    q3 = run_q3()
    cases = pilot()
    chosen, compiled, costs, comparisons = benchmark(cases, snapshot)
    noisy = benchmark_noise(compiled, snapshot)
    exact = grouped(cases, [row["p_exact"] for row in comparisons[chosen]])
    ideal = grouped(cases, [row["p_compiled_ideal_aer"] for row in comparisons[chosen]])
    grouped_noise = {name: grouped(cases, values) for name, values in noisy.items()}
    cycles = {}
    for time in TIMES:
        signal, reference = (f"{arm}_t{time:.1f}" for arm in ("signal", "reference"))
        sources = {"compiled_ideal_aer": (ideal[signal], ideal[reference])}
        sources.update({name: (values[signal], values[reference]) for name, values in grouped_noise.items()})
        primary_counts = np.rint(SHOT_LEVELS[0]*np.asarray(sources["calibrated_aer"][0])).astype(int)
        primary_ref = np.rint(SHOT_LEVELS[0]*np.asarray(sources["calibrated_aer"][1])).astype(int)
        cycles[f"t{time:.1f}"] = {
            "exact_signal_Z": complex_record(harmonic(exact[signal])),
            "exact_reference_Z": complex_record(harmonic(exact[reference])),
            "calibrated_aer_signal_Z": complex_record(harmonic(sources["calibrated_aer"][0])),
            "calibrated_aer_relative_phase_rad": float(np.angle(
                harmonic(sources["calibrated_aer"][0])*harmonic(sources["calibrated_aer"][1]).conj(),
            )),
            "four_vs_eight_and_dense_aliasing": aliasing(time, PLANTED_PHASE+REFERENCE_OFFSET),
            "planned_intervals_rounded_calibrated_counts": estimate(primary_counts, primary_ref, SHOT_LEVELS[0]),
            "planned_acceptance_at_calibrated_means": acceptance(
                primary_counts, SHOT_LEVELS[0], harmonic(exact[signal]), [values[signal] for values in grouped_noise.values()],
            ),
            "shot_monte_carlo": shot_benchmark(time, sources),
            "conditional_fisher_bounds": [fisher(time, shots=shots) for shots in SHOT_LEVELS],
        }
    path = out / "q2_isa.qpy"
    with path.open("wb") as handle:
        qpy.dump([embed(circuit, snapshot) for circuit in compiled], handle)
    input_snapshot = out / "calibration.json"
    if snapshot_path.resolve() != input_snapshot.resolve():
        write(input_snapshot, snapshot)
    outputs = out / "q2_cases.csv"
    with outputs.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["case_id", "arm", "time", "quadrant", "theta", "phase_programmed",
                         "exact", "compiled_aer_ideal", *noisy.keys()])
        for index, (case, row) in enumerate(zip(cases, comparisons[chosen], strict=True)):
            writer.writerow([case.id, case.arm, case.time, case.quadrant, case.theta, case.phase,
                             row["p_exact"], row["p_compiled_ideal_aer"], *(values[index] for values in noisy.values())])
    manifest = {
        "protocol": PROTOCOL, "prepared_utc": now(), "evidence": "simulation only",
        "target_type": snapshot["target_type"], "backend": snapshot["backend"],
        "physical_pair_xy": snapshot["physical_pair_xy"], "calibration_timestamp": snapshot["calibration_timestamp"],
        "calibration_id": snapshot["calibration_id"], "calibration_sha256": digest(input_snapshot),
        "qpy_sha256": digest(path), "selected_synthesis": chosen, "synthesis_bakeoff": costs,
        "case_order": [case.id for case in cases], "cases": [case.record() for case in cases],
        "primary": {"signal": f"signal_t{PRIMARY_TIME:.1f}", "reference": f"reference_t{PRIMARY_TIME:.1f}",
                    "per_setting_shots": SHOT_LEVELS[0], "systematic_floor_per_component": SYSTEMATIC_FLOOR},
        "seeds": {"transpiler": SEED, "case_order": ORDER_SEED, "monte_carlo": MC_SEED, "aer": 271828},
        "monte_carlo_replicates_per_configuration": REPLICATES,
        "budget": {str(shots): budget(comparisons[chosen], shots) for shots in SHOT_LEVELS},
    }
    write(out / "manifest.json", manifest)
    write(out / "mathematical_audit.json", checks)
    write(out / "q2_compilation.json", comparisons)
    write(out / "q2_protocol.json", {"scans": {"exact": exact, "compiled_ideal": ideal, **grouped_noise},
                                   "phase_analysis": cycles})
    write(out / "q3_curvature.json", q3)
    return manifest


def _credential(path):
    if path:
        text = path.read_text(encoding="utf-8-sig").strip()
        if not text.startswith("{"):
            return text
        fields = json.loads(text)
        key = fields.get("apikey") or fields.get("api_key") or fields.get("token")
        if isinstance(key, str) and key:
            return key
        raise Hold("the key file must contain key text or IBM API-key JSON")
    for variable in ("QISKIT_IBM_TOKEN", "IBM_QUANTUM_API_KEY"):
        if token := os.getenv(variable):
            return token
    options = QiskitRuntimeService.saved_accounts(default=True, channel="ibm_quantum_platform")
    if len(options) == 1:
        return next(iter(options.values()))["token"]
    raise Hold("no default IBM credential; use a supported environment variable or --token-file")


def live_service(path=None, instance=None):
    token = _credential(path)
    discovery = QiskitRuntimeService(
        channel="ibm_quantum_platform", token=token, instance="auto", plans_preference=["open"],
    )
    instances = [row for row in discovery.instances() if row.get("plan") == "open"
                 and row.get("pricing_type", "free") == "free"
                 and (instance is None or instance in (row["name"], row["crn"]))]
    if len(instances) != 1:
        raise Hold("select one existing verified Open Plan instance")
    return QiskitRuntimeService(channel="ibm_quantum_platform", token=token, instance=instances[0]["crn"])


def free_balance(service):
    crn = service.active_instance()
    if not crn or not any(row["crn"] == crn and row.get("plan") == "open"
                         and row.get("pricing_type", "free") == "free" for row in service.instances()):
        raise Hold("active IBM instance is not verified as Open Plan")
    usage = service.usage()
    values = [usage.get("usage_remaining_seconds")]
    if isinstance(usage.get("usage_remaining_ru"), (int, float)):
        values.append(60 * usage["usage_remaining_ru"])
    values = [float(value) for value in values if isinstance(value, (int, float)) and np.isfinite(value)]
    if not values:
        raise Hold("IBM did not report remaining allocation")
    remaining = 0 if usage.get("usage_limit_reached") else max(0, min(values))
    return {"plan": "open", "checked_utc": now(), "remaining_qpu_seconds": remaining}


def submission(service, out, shots, *, authorized=False):
    if not authorized:
        raise Hold("hardware submission requires separate approval and --confirm-free-qpu")
    manifest = load(out / "manifest.json")
    if manifest["target_type"] != "live_snapshot" or shots not in SHOT_LEVELS:
        raise Hold("a live calibration and a prespecified shot level are required")
    snapshot, qpy_path = out / "calibration.json", out / "q2_isa.qpy"
    if digest(snapshot) != manifest["calibration_sha256"] or digest(qpy_path) != manifest["qpy_sha256"]:
        raise Hold("simulation or ISA receipt integrity check failed")
    estimate = manifest["budget"][str(shots)]
    account = free_balance(service)
    if estimate["unknown_instruction_durations"] or account["remaining_qpu_seconds"] < estimate["required_free_qpu_seconds"]:
        raise Hold("insufficient verified free time or incomplete gate timing")
    backend = service.backend(manifest["backend"], instance=service.active_instance())
    props = backend.properties()
    if not backend.status().operational or backend.configuration().simulator or not props:
        raise Hold("the prepared backend is no longer an operational QPU")
    if props.last_update_date.isoformat() != manifest["calibration_timestamp"]:
        raise Hold("capture a fresh calibration and regenerate simulations before submitting")
    if getattr(backend, "calibration_id", None) != manifest["calibration_id"]:
        raise Hold("backend calibration ID has changed")
    with qpy_path.open("rb") as stream:
        circuits = qpy.load(stream)
    if [c.metadata["case_id"] for c in circuits] != manifest["case_order"]:
        raise Hold("the proposed IBM circuit order differs from the registered workload")
    tag = f"ahr-qpu-01-{uuid4().hex[:16]}"
    cap = estimate["required_free_qpu_seconds"]
    sampler = SamplerV2(mode=backend, options={
        "max_execution_time": cap, "environment": {"job_tags": [tag]},
        "twirling": {"enable_gates": False, "enable_measure": False},
        "dynamical_decoupling": {"enable": False},
    })
    checkpoint = out / "hardware_job.json"
    record = {"tag": tag, "job_id": None, "submitted_utc": now(), "backend": backend.name,
              "shots_per_circuit": shots, "free_balance_checked": account, "max_execution_time_s": cap}
    with checkpoint.open("x", encoding="utf-8") as stream:
        json.dump(record, stream, indent=2)
    record["job_id"] = sampler.run(circuits, shots=shots).job_id()
    write(checkpoint, record)
    return record


def collect(service, out):
    free_balance(service)
    record = load(out / "hardware_job.json")
    if record["job_id"] is None:
        matches = service.jobs(job_tags=[record["tag"]], instance=service.active_instance(), limit=2)
        if len(matches) != 1:
            raise Hold("use the recorded job tag in IBM Workloads to resolve submission status")
        record["job_id"] = matches[0].job_id()
        write(out / "hardware_job.json", record)
    job = service.job(record["job_id"])
    status = job.status()
    if status != "DONE":
        return {"job_id": record["job_id"], "status": status}
    manifest = load(out / "manifest.json")
    result = job.result()
    counts = {key: pub.data.out.get_counts() for key, pub in zip(manifest["case_order"], result, strict=True)}
    shots = record["shots_per_circuit"]
    if any(sum(values.values()) != shots or set(values).difference({"00", "01", "10", "11"})
           for values in counts.values()):
        raise Hold("IBM counts do not match the registered shot and outcome space")
    measured = {}
    for case in manifest["cases"]:
        key = f'{case["arm"]}_t{case["time"]:.1f}'
        measured.setdefault(key, [None]*4)[case["quadrant"]] = counts[case["id"]].get("00", 0)
    references = load(out / "q2_protocol.json")["scans"]
    primary = manifest["primary"]
    signal, ref = primary["signal"], primary["reference"]
    data = {
        **record, "status": "DONE", "counts_source": "IBM Quantum hardware", "retrieved_utc": now(),
        "qpu_seconds": job.usage(), "counts": counts,
        "primary_phase": estimate(measured[signal], measured[ref], shots),
        "primary_acceptance": acceptance(
            measured[signal], shots, harmonic(references["exact"][signal]),
            [rows[signal] for name, rows in references.items() if name not in {"exact", "compiled_ideal"}],
        ),
    }
    write(out / "hardware_counts.json", data)
    return data


def main(argv=None):
    parser = argparse.ArgumentParser(prog="experiment.py")
    commands = parser.add_subparsers(dest="command", required=True)
    simulation = commands.add_parser("simulate")
    simulation.add_argument("--snapshot", type=Path, default=ROOT / "receipts/calibration.json")
    simulation.add_argument("--out", type=Path, required=True)
    calibration = commands.add_parser("capture")
    calibration.add_argument("--output", type=Path, required=True)
    calibration.add_argument("--backend")
    submit = commands.add_parser("submit")
    submit.add_argument("--out", type=Path, required=True)
    submit.add_argument("--shots", type=int, choices=SHOT_LEVELS, default=SHOT_LEVELS[0])
    submit.add_argument("--confirm-free-qpu", action="store_true", required=True)
    retrieve = commands.add_parser("collect")
    retrieve.add_argument("--out", type=Path, required=True)
    for command in (calibration, submit, retrieve):
        command.add_argument("--token-file", type=Path)
        command.add_argument("--instance")
    args = parser.parse_args(argv)
    if args.command == "simulate":
        result = simulate(args.snapshot, args.out)
        print(json.dumps({"selected": result["selected_synthesis"], "budget": result["budget"]}, indent=2))
        return 0
    logging.getLogger("qiskit_ibm_runtime").setLevel(logging.CRITICAL)
    try:
        service = live_service(args.token_file, args.instance)
        if args.command == "capture":
            account = free_balance(service)
            backend = (service.backend(args.backend, instance=service.active_instance()) if args.backend
                       else service.least_busy(instance=service.active_instance(), operational=True, simulator=False))
            if not backend.status().operational or backend.configuration().simulator:
                raise Hold("snapshot must use an operational QPU")
            result = capture(backend, account=account, live=True)
            write(args.output, result)
            result = {"backend": result["backend"], "physical_pair_xy": result["physical_pair_xy"], "account": account}
        elif args.command == "submit":
            result = submission(service, args.out, args.shots, authorized=args.confirm_free_qpu)
        else:
            result = collect(service, args.out)
    except Hold as exc:
        print(f"HOLD: {exc}")
        return 2
    except (QiskitError, RequestsApiError, RequestException, OSError, ValueError) as exc:
        print(f"HOLD: IBM operation failed ({type(exc).__name__})")
        return 2
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
