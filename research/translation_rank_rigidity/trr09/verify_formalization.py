#!/usr/bin/env python3
"""Build and audit the actual finite coefficient and residue exclusion proofs."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
BASE_PATH = HERE.parent / "trr08" / "verify_formalization.py"
SPEC = importlib.util.spec_from_file_location("trr08_verifier", BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("Cannot load the TRR-08 verification contract")
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)

# Reviewed declaration contract. This list is independent of the source and
# the compiler output read by main().
NEW_REPORTS = {
    "NormalizedSlope": (
        "normalizedSlope_of_x_ne", "normalizedSlope_comm", "affineX_neg",
        "affineY_neg", "normalizedSlope_self", "normalizedSlope_add_x",
        "normalizedSlope_add_y", "normalizedSlope_line", "normalizedSlope_chord",
        "normalizedSlope_neg_both", "normalizedSlope_rotate", "normalizedSlope_sum_neg",
        "normalizedSlope_diagonal_generic", "normalizedSlope_diagonal_double",
    ),
    "DiagonalSlope": ("normalizedSlope_of_add_eq_zero", "normalizedSlope_diagonal"),
    "FiniteSlopeAverage": (
        "translate_row_sum", "rowSum_add_of_identity", "rowSum_add",
        "coefficient_add_nsmul_of_identity", "coefficient_add_nsmul", "coefficient_zero",
        "coefficient_add", "coefficient_double", "coefficient_double_of_diagonal",
        "coefficientSequence_add", "coefficientSequence_double", "cyclic_card",
        "cyclicCoefficient_add", "cyclicCoefficient_double",
        "cyclicCoefficient_double_of_diagonal",
    ),
    "LocalCoefficient": (
        "normalizedSlope_pair", "slopeCoefficient_eq_unpaired", "coefficientOthers_image",
        "coefficientOthers_fiber", "coefficientOthers_sum_by_roots",
        "localCoefficient_eq_slopeCoefficient",
    ),
    "BarycentricResidue": (
        "cofactor_value_ne_zero", "basis_derivative_at_other", "weighted_reciprocal_sum",
        "weighted_reciprocal_square_sum", "nodal_derivative_eval",
        "nodal_second_derivative_eval", "finite_residue_identity",
    ),
    "TraceCoefficient": (
        "coefficient_sum_split", "coefficientOthers_card_cast", "paired_add_x",
        "subgroupXTrace_translate", "subgroupXTrace_translate_others",
        "subgroupXTrace_eq_reciprocal", "localSecondCoefficient_relation",
    ),
    "ExplicitObstruction": (
        "slopeCoefficient_double", "slopeCoefficient_double_tangent", "localCoefficient_double",
        "cyclicSlopeCoefficient_double", "cyclicSlopeCoefficient_double_tangent",
        "tame_cyclicSlopeCoefficient_exclusion",
    ),
    "CyclicCoefficient": ("cyclic_ne_neg_of_odd_order", "localCoefficient_cyclic_eq"),
    "ResidueEigenvector": (
        "subgroupResidue_eq_inverse_product", "subgroupResidue_ne_zero",
        "paired_add_x_difference", "residue_summand_pair", "residueMatrixRow_by_roots",
        "residueMatrixRow_eq_localSecondCoefficient", "residue_eigenvector_localSecondCoefficient",
        "residue_eigenvector_square", "residue_eigenvector_explicit_square",
    ),
    "TameEigenvector": (
        "tame_cyclicResidue_eigenvector_exclusion", "tame_no_cyclicResidue_eigenvector",
    ),
}
NEW_MODULES = [
    ("geometry", f"TRR08Geometry/{module}.lean", [
        "TRR08Geometry." +
        (module + "." if module in {"FiniteSlopeAverage", "BarycentricResidue"} else "") + name
        for name in names
    ]) for module, names in NEW_REPORTS.items()
]
MODULES = BASE.MODULES + NEW_MODULES

BOUNDARY = {
    "full_interpolation_theorem_formalized": False,
    "actual_residue_eigenvector_exclusion_formalized": True,
    "main_theorem": "TRR08Geometry.tame_cyclicResidue_eigenvector_exclusion",
    "hypotheses": [
        "K is a field; W is an actual Mathlib smooth short Weierstrass curve.",
        "T has finite odd order N >= 19; the image of N in K is nonzero.",
        "The images of 2 and 3 in K are nonzero.",
        "The actual residues lambda(P)=1/(2*y(P)*product_{v!=x(P)}(x(P)-v)) satisfy M0*lambda=u*lambda on the nonidentity subgroup points.",
    ],
    "derived_in_lean": [
        "Every identity, inverse and tangent case of the diagonal slope cocycle.",
        "The explicit reciprocal-root coefficient equals the negative finite slope sum.",
        "Finite averaging proves the coefficient doubling law.",
        "Lagrange interpolation proves the finite weighted reciprocal identity.",
        "The actual residue row equals the second local coefficient times the residue.",
        "Translation and inversion of the finite subgroup give the common coordinate trace.",
        "The eigenvector condition implies the square identity; nine subgroup x-coordinates give the degree-eight contradiction.",
    ],
    "remaining_obligations": [
        "Identify the geometric evaluation image with the residue hyperplane.",
        "Interpret finite feature tensors as coordinate polynomials with the stated block degree.",
        "Transfer general Weierstrass models to short form with degree preservation.",
        "Formalize the remaining function-field and divisor argument when the characteristic divides the marked order.",
        "Integrate the small-order integral certificates with the geometric theorem in Lean.",
    ],
}


def guard_source(text: str, path: str) -> None:
    if re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", text):
        raise ValueError(f"Forbidden proof admission or unchecked computation: {path}")


def source_report_contract(source: str, relative: str, expected: list[str]) -> None:
    names = re.findall(r"^#print axioms\s+(\S+)", source, re.M)
    if relative.startswith("MathCan/"):
        prefix = "MathCan." + Path(relative).stem + "."
    elif Path(relative).stem in {"FiniteSlopeAverage", "BarycentricResidue"}:
        prefix = "TRR08Geometry." + Path(relative).stem + "."
    else:
        prefix = "TRR08Geometry."
    names = [name if "." in name else prefix + name for name in names]
    if names != expected:
        raise ValueError(f"Source declaration contract mismatch: {relative}")


def reject_wrong_residue_identity(lake: str, geometry: Path, logs: Path) -> dict:
    """The normal Lean compiler must reject a changed mathematical conclusion."""
    source = geometry / "TRR08Geometry/BarycentricResidue.lean"
    original = source.read_text()
    anchor = ("theorem finite_residue_identity (hv : Set.InjOn v s) (hi : i ∈ s) :\n"
              "    2 * (cofactor s v i).eval (v i) *")
    if original.count(anchor) != 1:
        raise ValueError("The mathematical mutation target has changed")
    modified = original.replace(anchor, anchor.replace("    2 *", "    3 *"), 1)
    theorem_start = modified.index("theorem finite_residue_identity")
    theorem_end = modified.index("\n#print axioms", theorem_start)
    first_line = modified[:theorem_start].count("\n") + 1
    last_line = modified[:theorem_end].count("\n") + 1
    with tempfile.TemporaryDirectory(prefix="trr09-lean-control-") as directory:
        bad = Path(directory) / "WrongResidueIdentity.lean"
        bad.write_text(modified)
        start = time.monotonic()
        result = subprocess.run([lake, "env", "lean", str(bad)], cwd=geometry,
                                capture_output=True, text=True, timeout=120)
        output = result.stdout + result.stderr
        (logs / "reject-wrong-residue-identity.log").write_text(output)
        if result.returncode == 0 or "error" not in output:
            raise ValueError("Lean failed to reject the changed residue identity")
        # Import failures would not test the changed conclusion.
        if any(term in output for term in ("unknown module prefix", "object file", "No such file")):
            raise ValueError("The mutation control failed before checking the changed proof")
        error_lines = [int(line) for line in re.findall(
            re.escape(bad.name) + r":(\d+):\d+: error\b", output)]
        if not any(first_line <= line <= last_line for line in error_lines):
            raise ValueError("The mutation was not rejected inside the changed theorem")
        return {"name": "residue_leading_factor_2_changed_to_3", "status": "rejected",
                "compiler_exit_code": result.returncode,
                "source_sha256": BASE.sha256(source), "mutated_sha256": BASE.sha256(bad),
                "changed_theorem_line_interval": [first_line, last_line],
                "compiler_error_lines": error_lines,
                "elapsed_seconds": round(time.monotonic() - start, 6)}


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
    receipt = {"schema": "trr09-formalization-v1", "status": "running",
               "checked_at_utc": datetime.now(timezone.utc).isoformat(),
               "proof_boundary": BOUNDARY, "modules": []}
    start = time.monotonic()
    try:
        version = BASE.run([args.lake, "env", "lean", "--version"], core,
                           logs / "lean-version.log", 30).stdout.strip()
        if "version 4.35.0" not in version:
            raise ValueError(f"Unexpected Lean version: {version}")
        receipt["lean_version"] = version
        geometry_version = BASE.run([args.lake, "env", "lean", "--version"], geometry,
                                    logs / "geometry-lean-version.log", 30).stdout.strip()
        if geometry_version != version:
            raise ValueError(f"Geometry Lean version differs from the core: {geometry_version}")
        receipt["geometry_lean_version"] = geometry_version
        manifest = json.loads((geometry / "lake-manifest.json").read_text())
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        installed = subprocess.check_output(["git", "rev-parse", "HEAD"],
                    cwd=geometry / ".lake/packages/mathlib", text=True).strip()
        if mathlib["rev"] != BASE.PINNED_MATHLIB or installed != BASE.PINNED_MATHLIB:
            raise ValueError("Mathlib differs from the reviewed revision")
        receipt.update({"mathlib_revision": installed,
            "geometry_manifest_sha256": BASE.sha256(geometry / "lake-manifest.json"),
            "verifier_sha256": BASE.sha256(Path(__file__)),
            "base_verifier_sha256": BASE.sha256(BASE_PATH)})
        BASE.run([args.lake, "build", "MathCan.TranslationInterpolationUniform",
                  "MathCan.TranslationInterpolationRootBound", "MathCan.TranslationInterpolationEvaluation"],
                 core, logs / "core-build.log", 600)
        BASE.run([args.lake, "build", "TRR08Geometry"], geometry, logs / "geometry-build.log", 1200)
        roots = {"core": core, "geometry": geometry}
        all_expected = [name for _, _, names in MODULES for name in names]
        if len(all_expected) != len(set(all_expected)) or len(all_expected) != 113:
            raise ValueError("The 43 plus 70 declaration contract has changed")
        for group, relative, expected in MODULES:
            source = roots[group] / relative
            code = source.read_text()
            guard_source(code, relative)
            source_report_contract(code, relative, expected)
            result = BASE.run([args.lake, "env", "lean", relative], roots[group],
                              logs / (source.stem + ".log"), 300)
            reports = BASE.parse_reports(result.stdout, expected)
            receipt["modules"].append({"project": group, "path": relative,
                "source_sha256": BASE.sha256(source), "principal_report_count": len(reports),
                "transitive_axioms": reports})
        receipt["principal_report_count"] = len(all_expected)
        receipt["new_principal_report_count"] = sum(len(names) for _, _, names in NEW_MODULES)
        receipt["mathematical_mutation_control"] = reject_wrong_residue_identity(args.lake, geometry, logs)
        receipt["status"] = "passed"
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError, StopIteration) as exc:
        receipt["status"] = "failed"
        receipt["error"] = str(exc)
    receipt["elapsed_seconds"] = round(time.monotonic() - start, 6)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": receipt["status"], "receipt": str(output),
                     "principal_reports": receipt.get("principal_report_count"),
                     "new_principal_reports": receipt.get("new_principal_report_count"),
                     "full_interpolation_theorem_formalized": False}), flush=True)
    return 0 if receipt["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
