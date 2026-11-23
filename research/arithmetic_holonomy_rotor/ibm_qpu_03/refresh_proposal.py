"""Recompile a proposal when calibration identity changes but its model is equivalent."""
import argparse
from hashlib import sha256
from pathlib import Path

from backend_snapshot import calibration_fingerprint, write_json
from run_study import Study, read


def text_digest(path):
    return sha256(path.read_text(encoding="utf-8").encode()).hexdigest()


def refresh(prior, snapshot_path, output):
    previous_calibration = read(prior / "calibration.json")
    previous_manifest = read(prior / "q3_candidate_manifest.json")
    fresh = read(snapshot_path)
    account = fresh["account"]
    if fresh["mode"] != "live_read_only" or account["plan"] != "open" or fresh["qpu_submitted"]:
        raise ValueError("a read-only free IBM snapshot is required")
    if text_digest(prior / "calibration.json") != previous_manifest["calibration_sha256"]:
        raise ValueError("prior manifest and archived calibration do not match")
    previous_qpy = sha256((prior / "q3_candidate_isa.qpy").read_bytes()).hexdigest()
    if previous_qpy != previous_manifest["qpy_sha256"]:
        raise ValueError("prior manifest and ISA circuits do not match")
    old_snapshot = previous_calibration["backend"]
    new_snapshot = fresh["backend"]
    old_model = calibration_fingerprint(old_snapshot, include_calibration_identity=False)
    new_model = calibration_fingerprint(new_snapshot, include_calibration_identity=False)
    if old_model != new_model:
        raise ValueError("the physical model changed; run the full study on the new calibration")
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / "calibration.json", fresh)
    statistics = read(prior / "statistics.json")["designs"]["likelihood"]
    study = Study(new_snapshot, previous_manifest["synthesis"])
    manifest = study.controls_and_manifest(
        previous_manifest["likelihood_time"], account, statistics, output
    )
    binding = ("case_id", "shots", "classical_bit_to_physical", "setting")
    if [[r[k] for k in binding] for r in manifest["settings"]] != [
            [r[k] for k in binding] for r in previous_manifest["settings"]]:
        raise ValueError("recompilation changed the cases or readout mapping; run the full study")
    keys = ("exact", "compiled", "aer")
    shifts = {k: max(abs(a[k] - b[k]) for a, b in zip(
        previous_manifest["settings"], manifest["settings"], strict=True)) for k in keys}
    if max(shifts.values()) > 1e-12:
        raise ValueError("recompiled predictions changed; run the full study on the new calibration")
    write_json(output / "q3_candidate_manifest.json", manifest)
    evidence = {
        "previous_manifest_sha256": text_digest(prior / "q3_candidate_manifest.json"),
        "refreshed_manifest_sha256": text_digest(output / "q3_candidate_manifest.json"),
        "previous_calibration_timestamp": old_snapshot["calibration_timestamp"],
        "refreshed_calibration_timestamp": new_snapshot["calibration_timestamp"],
        "simulation_inputs_sha256": new_model,
        "previous_statistics_sha256": text_digest(prior / "statistics.json"),
        "max_return_probability_changes": shifts,
        "case_order_shots_and_readout_maps_unchanged": True,
        "original_submission_held_for_calibration_change": True,
        "qpu_submitted": False,
    }
    write_json(output / "refresh_evidence.json", evidence)
    return manifest, evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prior", required=True, type=Path)
    parser.add_argument("--snapshot", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    _, evidence = refresh(args.prior, args.snapshot, args.output)
    print(f"Refreshed manifest SHA-256 {evidence['refreshed_manifest_sha256']}")


if __name__ == "__main__":
    main()
