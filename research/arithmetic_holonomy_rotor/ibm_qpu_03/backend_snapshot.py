"""Read-only IBM inventory and a portable compact Target/Aer snapshot."""
import argparse
import json
from datetime import datetime, timedelta, timezone
from hashlib import sha256
from itertools import combinations
from pathlib import Path

import numpy as np

NATIVE = ("cz", "ecr", "cx")
OPERATIONS = (*NATIVE, "rz", "sx", "x", "id", "measure", "reset")


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n", encoding="utf-8", newline="\n")


def calibration_fingerprint(snapshot, *, include_calibration_identity=True):
    """Hash the calibrated simulation inputs independently of Aer-generated IDs."""
    keys = ("backend", "backend_width", "dt_s", "rep_delay_s", "instructions")
    if include_calibration_identity:
        keys = (*keys, "calibration_timestamp", "calibration_id")
    channel = {k: snapshot[k] for k in keys}
    channel["physical_xyz"] = snapshot["selection"]["physical_xyz"]
    channel["instructions"] = sorted(channel["instructions"],
                                     key=lambda row: (row["gate"], row["physical"]))
    channel["noise"] = sorted(json.dumps({k: v for k, v in row.items() if k != "id"},
                                         sort_keys=True, separators=(",", ":"))
                              for row in snapshot["noise"]["errors"])
    payload = json.dumps(channel, sort_keys=True, separators=(",", ":")).encode()
    return sha256(payload).hexdigest()


def compare_captures(initial, later):
    a = calibration_fingerprint(initial["backend"])
    b = calibration_fingerprint(later["backend"])
    return {"initial_account_check": initial["account"], "repeat_account_check": later["account"],
            "initial_calibration_fingerprint": a, "repeat_calibration_fingerprint": b,
            "same_compilation_and_noise_inputs": a == b, "repeat_devices": later["devices"],
            "repeat_selection": later["backend"]["selection"], "qpu_submitted": False}


def rank_triples(target, previous=None):
    readout = {q[0]: p for q, p in target["measure"].items()
               if q and p is not None and p.error is not None and p.duration is not None}
    links = {}
    known = previous or {}
    for name in set(NATIVE) & set(target.operation_names):
        for pair, p in target[name].items():
            if (not pair or p is None or p.error is None or p.duration is None or
                    not all(q in readout for q in pair)):
                continue
            key = tuple(sorted(pair))
            old = known.get((name, *pair))
            drift = abs(p.error - old) if old is not None else 0.0
            score = p.error + 3500 * p.duration + 2 * drift
            row = {"gate": name, "physical": list(pair), "error": p.error,
                   "duration_s": p.duration, "error_change": drift if old is not None else None}
            if key not in links or score < links[key][0]:
                links[key] = (score, row)
    triples = []
    for middle in sorted(readout):
        neighbors = sorted(q for q in readout if tuple(sorted((q, middle))) in links)
        for left, right in combinations(neighbors, 2):
            physical = [left, middle, right]
            bonds = [links[tuple(sorted((q, middle)))] for q in (left, right)]
            measurements = [readout[q].error for q in physical]
            triples.append({"physical_xyz": physical,
                            "score": 8 * sum(score for score, _ in bonds) + sum(measurements),
                            "bonds": [row for _, row in bonds], "readout_errors": measurements,
                            "contains_q2_pair": {9, 10}.issubset(physical)})
    return sorted(triples, key=lambda r: (r["score"], r["physical_xyz"]))


def capture(backend, selection):
    from qiskit_aer.noise import NoiseModel

    target = backend.target
    physical = selection["physical_xyz"]
    instructions = []
    for name in sorted(set(OPERATIONS) & set(target.operation_names)):
        for qubits, p in target[name].items():
            if qubits and set(qubits) <= set(physical):
                instructions.append({"gate": name, "physical": list(qubits),
                                     "error": p.error if p else None,
                                     "duration_s": p.duration if p else None})
    reduced = []
    for entry in NoiseModel.from_backend(backend).to_dict(serializable=True)["errors"]:
        if "gate_qubits" not in entry:
            reduced.append(entry)
            continue
        scopes = [[physical.index(q) for q in qubits] for qubits in entry["gate_qubits"]
                  if set(qubits) <= set(physical)]
        if scopes:
            reduced.append({**entry, "gate_qubits": scopes})
    config = backend.configuration()
    return {"backend": backend.name, "backend_width": backend.num_qubits,
            "calibration_timestamp": backend.properties().last_update_date.isoformat(),
            "calibration_id": getattr(backend, "calibration_id", None),
            "dt_s": target.dt, "rep_delay_s": getattr(config, "default_rep_delay", None),
            "selection": selection, "instructions": instructions, "noise": {"errors": reduced}}


def open_account(config_path):
    from qiskit_ibm_runtime import QiskitRuntimeService

    config = json.loads(Path(config_path).read_text(encoding="utf-8-sig"))
    if not isinstance(config, dict):
        raise ValueError("expected an IBM JSON object")
    if "token" in config or "apikey" in config or "api_key" in config:
        saved = config
    else:
        compatible = [value for value in config.values()
                      if isinstance(value, dict) and value.get("channel") == "ibm_quantum_platform"]
        defaults = [value for value in compatible if value.get("is_default_account")]
        candidates = defaults or compatible
        if len(candidates) != 1:
            raise ValueError("select one saved IBM Quantum Platform account")
        saved = candidates[0]
    token = saved.get("token") or saved.get("apikey") or saved.get("api_key")
    if not isinstance(token, str) or not token.strip():
        raise ValueError("no key in selected IBM account")
    platform = {"token": token, "channel": "ibm_quantum_platform"}
    discovery = QiskitRuntimeService(instance="auto", plans_preference=["open"], **platform)
    pinned = saved.get("instance")
    instances = [r for r in discovery.instances()
                 if r.get("plan") == "open" and r.get("pricing_type", "free") == "free"
                 and (pinned in (None, "", "auto") or pinned in (r.get("name"), r.get("crn")))]
    if len(instances) != 1:
        raise ValueError("expected one uniquely selected free Open Plan instance")
    crn = instances[0]["crn"]
    service = QiskitRuntimeService(instance=crn, **platform)
    if service.active_instance() != crn:
        raise ValueError("selected Open Plan instance did not remain active")
    return service, crn


def historical_errors(backend, latest):
    """Use IBM's most recent calibration prior to the current one, if accessible."""
    cutoff = latest.last_update_date - timedelta(seconds=1)
    try:
        prior = backend.properties(datetime=cutoff)
    except Exception as exc:
        return {}, {"status": "unavailable", "error_type": type(exc).__name__}
    if prior is None or prior.last_update_date > cutoff:
        return {}, {"status": "no_distinct_prior_calibration"}
    errors = {}
    for gate in prior.gates:
        if gate.gate not in NATIVE:
            continue
        for parameter in gate.parameters:
            if parameter.name == "gate_error" and np.isfinite(parameter.value):
                errors[(gate.gate, *gate.qubits)] = float(parameter.value)
    return errors, {"status": "available", "prior_timestamp": prior.last_update_date.isoformat(),
                    "prior_native_couplers": len(errors)}


def live_inventory(config_path, previous_path=None, include_historical_drift=False):
    service, crn = open_account(config_path)
    usage = service.usage()
    seconds = usage.get("usage_remaining_seconds")
    ru = usage.get("usage_remaining_ru")
    values = [v for v in (seconds, 60 * ru if isinstance(ru, (int, float)) else None)
              if isinstance(v, (int, float)) and np.isfinite(v)]
    if not values:
        raise ValueError("IBM did not report free seconds or remaining RUs")
    free = max(0, min(values)) if not usage.get("usage_limit_reached") else 0
    checked = datetime.now(timezone.utc).isoformat()
    previous = json.loads(Path(previous_path).read_text(encoding="utf-8")) if previous_path else {}
    devices, eligible = [], []
    for backend in service.backends(operational=True, simulator=False, instance=crn):
        properties = backend.properties()
        if not properties:
            continue
        old = {(r["gate"], *r["physical"]): r["error"]
               for r in previous.get("backend", {}).get("instructions", [])
               if r["error"] is not None and previous["backend"]["backend"] == backend.name}
        drift = {"status": "previous_capture" if old else "unmeasured"}
        if include_historical_drift:
            historical, drift = historical_errors(backend, properties)
            if historical:
                old = historical
        triples = rank_triples(backend.target, old)
        if triples:
            devices.append({"backend": backend.name, "available_triples": len(triples),
                            "calibration_timestamp": properties.last_update_date.isoformat(),
                            "calibration_drift": drift,
                            "top_triples": triples[:5],
                            "best_q2_pair_extension": next(
                                (r for r in triples if r["contains_q2_pair"]), None)})
            eligible.append((triples[0]["score"], backend.name, backend, triples[0]))
    if not eligible:
        raise ValueError("no calibrated connected triples")
    _, _, backend, selection = min(eligible, key=lambda item: item[:2])
    snapshot = capture(backend, selection)
    return {"mode": "live_read_only", "checked_utc": checked,
            "account": {"plan": "open", "remaining_qpu_seconds": free, "checked_utc": checked},
            "devices": devices, "backend": snapshot, "previous_capture_utc": previous.get("checked_utc"),
            "qpu_submitted": False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--credential-file", required=True)
    p.add_argument("--previous")
    p.add_argument("--include-historical-drift", action="store_true")
    p.add_argument("--output", required=True)
    args = p.parse_args()
    try:
        report = live_inventory(args.credential_file, args.previous, args.include_historical_drift)
    except Exception as exc:
        # Cloud exceptions may include account identifiers in text.
        p.exit(1, f"Read-only inventory failed ({type(exc).__name__}). No job was submitted.\n")
    write_json(args.output, report)
    print(f"Read-only capture: {report['backend']['backend']}, {report['account']['remaining_qpu_seconds']} free seconds")


if __name__ == "__main__":
    main()
