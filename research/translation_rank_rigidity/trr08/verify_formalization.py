#!/usr/bin/env python3
"""Build and audit the TRR-08 Lean declarations and their geometric boundary."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
PINNED_MATHLIB = "56a005855ea17e0b0958f73ec801ae140b0a1679"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# These are an explicit contract, rather than a count inferred from source text.
MODULES = [
    ("core", "MathCan/TranslationInterpolationUniform.lean", [
        "MathCan.TranslationInterpolationUniform." + name for name in (
            "product_nonzero", "power_nonzero", "cancel_nonzero", "normalized_singular",
            "second_branch_five_nonzero",
            "leading_coefficients_force_singularity",
        )
    ]),
    ("core", "MathCan/TranslationInterpolationRootBound.lean", [
        "MathCan.TranslationInterpolationRootBound." + name for name in (
            "evaluate_quotient_cons", "synthetic_division", "quotient_length",
            "zero_of_quotient", "coefficients_zero_of_distinct_roots",
            "obstruction_evaluation", "obstruction_roots_force_singularity",
            "nonsingular_obstruction_root_exclusion", "doubling_implies_obstruction",
            "doubling_data_force_singularity", "nonsingular_doubling_data_exclusion",
        )
    ]),
    ("core", "MathCan/TranslationInterpolationEvaluation.lean", [
        "MathCan.TranslationInterpolationEvaluation." + name for name in (
            "span_iff_annihilated", "symmetric_decoder_reconstruction",
            "symmetric_decoder_iff", "decoder_coefficients_unique", "dot_pointMass",
            "assigned_row_iff_eigenvector", "pole_decoder_iff_eigenvector",
            "assigned_value_unique", "feature_tensor_annihilated",
            "evaluation_hyperplane_decoder_iff", "evaluation_columns_decoder_iff",
            "evaluation_pole_decoder_iff",
        )
    ]),
    ("geometry", "TRR08Geometry/MarkedPoints.lean", [
        "TRR08Geometry." + name for name in (
            "affineX_eq_iff", "firstNine_ne_zero", "firstNine_injective",
            "firstNine_ne_neg", "firstNine_x_injective", "tangent_denominator_ne_zero",
            "firstNine_tangent_denominator_ne_zero", "short_curve_equation",
            "short_discriminant_ne_zero", "short_y_ne_zero", "short_doubling_x",
        )
    ]),
    ("geometry", "TRR08Geometry/Obstruction.lean", [
        "TRR08Geometry.tame_coefficient_exclusion",
    ]),
    ("geometry", "TRR08Geometry/PointIdeals.lean", [
        "TRR08Geometry.nonidentity_point_class_ne_zero",
        "TRR08Geometry.point_ideal_ne_single_generator",
    ]),
]

BOUNDARY = {
    "full_interpolation_theorem_formalized": False,
    "actual_curve_tame_theorem": "TRR08Geometry.tame_coefficient_exclusion",
    "actual_curve_hypotheses": [
        "K is a field; W is an actual Mathlib smooth short Weierstrass curve.",
        "N = addOrderOf T >= 19; n = (N : K) is nonzero.",
        "The images of 2 and 3 in K are nonzero.",
        "a(k)^2 = n*(x(kT)+c) at every nonidentity multiple.",
        "a(2k) = 2*a(k)+n*(3*x(kT)^2+A)/(2*y(kT)) when kT and 2kT are nonidentity.",
    ],
    "tame_conclusion": "The hypotheses imply False.",
    "remaining_obligations": [
        "Construct the coefficients a from the rational function 1/Phi(x).",
        "Derive the square identity from the eigenvector condition via residues.",
        "Prove the logarithmic-derivative addition identity giving the doubling cocycle.",
        "Identify the geometric evaluation image with the residue hyperplane.",
        "Interpret finite feature tensors as coordinate polynomials with the stated block degree.",
        "Transfer generalized Weierstrass models to short form with degree preservation.",
        "Prove the function-field differential kernel and global-divisor-to-affine-ideal step in matching characteristic.",
        "Integrate the small-order certificates with the geometric theorem in Lean.",
    ],
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_reports(output: str, expected: list[str]) -> dict[str, list[str]]:
    rows = re.findall(
        r"'([^']+)' (?:depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)",
        output, re.S,
    )
    reports = {}
    for name, values in rows:
        if name in reports:
            raise ValueError(f"Duplicate axiom report: {name}")
        axioms = [v.strip() for v in values.replace("\n", " ").split(",") if v.strip()]
        if set(axioms) - ALLOWED_AXIOMS:
            raise ValueError(f"Unexpected transitive axioms for {name}: {axioms}")
        reports[name] = axioms
    if set(reports) != set(expected):
        raise ValueError(f"Axiom report mismatch: missing={set(expected)-set(reports)}, extra={set(reports)-set(expected)}")
    return reports


def run(command: list[str], cwd: Path, log: Path, seconds: int) -> subprocess.CompletedProcess:
    start = time.monotonic()
    print(f"Checking {log.stem}", flush=True)
    try:
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=seconds)
    except subprocess.TimeoutExpired as exc:
        raw = (exc.stdout or b"") + (exc.stderr or b"")
        log.write_bytes(raw if isinstance(raw, bytes) else raw.encode())
        raise RuntimeError(f"Time budget exceeded: {log.name}") from exc
    log.write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}); see {log}")
    print(f"Passed {log.stem} in {time.monotonic()-start:.1f}s", flush=True)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core-root", type=Path, default=HERE.parents[2])
    parser.add_argument("--geometry-root", type=Path)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output", type=Path, default=HERE / "formalization_receipt.json")
    args = parser.parse_args()
    core = args.core_root.resolve()
    geometry = (args.geometry_root or core / "experiments/trr08_geometry").resolve()
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    logs = output.parent / (output.stem + "_logs")
    logs.mkdir(exist_ok=True)
    receipt = {
        "schema": "trr08-formalization-v1",
        "status": "running",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "proof_boundary": BOUNDARY,
        "modules": [],
    }
    start = time.monotonic()
    try:
        version = run([args.lake, "env", "lean", "--version"], core, logs / "lean-version.log", 30).stdout.strip()
        if "version 4.35.0" not in version:
            raise ValueError(f"Unexpected Lean version: {version}")
        receipt["lean_version"] = version
        manifest = json.loads((geometry / "lake-manifest.json").read_text())
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        if mathlib["rev"] != PINNED_MATHLIB:
            raise ValueError("Mathlib manifest differs from the reviewed revision")
        installed = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=geometry / ".lake/packages/mathlib", text=True,
        ).strip()
        if installed != PINNED_MATHLIB:
            raise ValueError("Installed Mathlib differs from the manifest")
        receipt["mathlib_revision"] = installed
        receipt["geometry_manifest_sha256"] = sha256(geometry / "lake-manifest.json")
        receipt["verifier_sha256"] = sha256(Path(__file__))
        run([args.lake, "build", "MathCan.TranslationInterpolationUniform",
             "MathCan.TranslationInterpolationRootBound", "MathCan.TranslationInterpolationEvaluation"],
            core, logs / "core-build.log", 600)
        run([args.lake, "build", "TRR08Geometry"], geometry, logs / "geometry-build.log", 1200)
        roots = {"core": core, "geometry": geometry}
        for group, relative, expected in MODULES:
            source = roots[group] / relative
            # Deliberately conservative: scan comments and strings too, avoiding
            # a partial Lean lexer that could hide a real admission token.
            code = source.read_text()
            if re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", code):
                raise ValueError(f"Forbidden proof admission or unchecked computation: {relative}")
            result = run([args.lake, "env", "lean", relative], roots[group], logs / (source.stem + ".log"), 300)
            reports = parse_reports(result.stdout, expected)
            receipt["modules"].append({
                "project": group, "path": relative, "source_sha256": sha256(source),
                "principal_report_count": len(reports), "transitive_axioms": reports,
            })
        receipt["principal_report_count"] = sum(m["principal_report_count"] for m in receipt["modules"])
        receipt["new_principal_report_count"] = sum(m["principal_report_count"] for m in receipt["modules"][1:])
        receipt["status"] = "passed"
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError, StopIteration) as exc:
        receipt["status"] = "failed"
        receipt["error"] = str(exc)
    receipt["elapsed_seconds"] = round(time.monotonic() - start, 6)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": receipt["status"], "receipt": str(output),
                      "principal_reports": receipt.get("principal_report_count"),
                      "full_interpolation_theorem_formalized": False}), flush=True)
    return 0 if receipt["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
