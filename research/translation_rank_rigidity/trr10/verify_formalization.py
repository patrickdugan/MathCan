#!/usr/bin/env python3
"""Audit the exact ordinary block-degree theorem and its inherited proofs."""
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
BASE_PATH = HERE.parent / "trr09" / "verify_formalization.py"
SPEC = importlib.util.spec_from_file_location("trr09_verifier", BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("Cannot load the TRR-09 verification contract")
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
CORE = BASE.BASE

# Reviewed declarations, independent of the source and compiler output read below.
NEW_REPORTS = {
    "RootCardinality": (
        "subgroupNonzero_x_fiber", "subgroupNonzero_sum_by_roots", "subgroupXRoots_card",
    ),
    "CubicMonomials": (
        "shortCubic_natDegree_le", "cubicMonomial_natDegree_le", "shortCubic_eval",
        "cubicMonomial_eval", "even_monomial_on_curve", "odd_monomial_on_curve",
    ),
    "ResidueAnnihilation": (
        "residueSum_add", "residueSum_const_mul", "residueSum_congr_nonzero",
        "residueSum_xFunction", "residueSum_yFunction", "residueSum_normalForm",
        "subgroupNodalWeight_eval_sum_eq_coeff", "residueSum_normalForm_eq_coeff",
        "residueSum_normalForm_eq_zero",
    ),
    "PolynomialDegree": (
        "bivariate_exponent_sum", "bivariate_support_totalDegree",
        "bivariate_support_weight_le", "bivariateEval_eq_sum",
        "sum_bivariateEval_eq_zero_of_moments",
        "sum_bivariateEval_eq_zero_of_weighted_moments",
    ),
    "ResidueMonomials": (
        "residueSum_even_monomial", "residueSum_odd_monomial",
        "residueSum_monomial_eq_zero", "sum_residue_monomial_eq_zero",
        "sum_residue_ordinary_monomial_eq_zero", "residue_bivariateEval_eq_zero",
    ),
    "BlockPolynomial": (
        "blockEval_eq_sum", "sum_blockEval_right_eq_zero_of_moments",
        "sum_blockEval_left_eq_zero_of_moments",
    ),
    "TameDecoder": (
        "assignedX_add", "assignedX_residue_row",
        "polynomialDecoder_eigenvector_of_moments", "polynomialDecoder_residue_eigenvector",
        "tame_polynomialDecoder_exclusion", "tame_no_polynomialDecoder",
        "tame_polynomialDecoder_degree_lower_bound",
    ),
    "PolynomialLift": (
        "cubicLiftBase_eval", "cubicLiftBase_totalDegree", "monomialLift_eval",
        "monomialLift_totalDegree_le", "oddMonomialLift_eval", "oddMonomialLift_totalDegree_le",
        "polynomialLift_eval", "oddPolynomialLift_eval", "polynomialLift_totalDegree_le",
        "oddPolynomialLift_totalDegree_le", "normalFormLift_eval", "normalFormLift_totalDegree_le",
    ),
    "PointInterpolation": (
        "subgroupPointInterpolator_eval", "subgroupPointInterpolator_totalDegree_le_roots",
        "subgroupPointInterpolator_totalDegree_le", "nonidentity_point_polynomial_family",
    ),
    "BlockTensor": (
        "BlockDegreeLE_monomial", "BlockDegreeLE_sum", "BlockDegreeLE_smul",
        "blockEval_tensor_monomial", "blockTensor_degree", "blockTensor_eval",
        "matrixPolynomial_degree", "matrixPolynomial_eval",
    ),
    "DecoderDegree": (
        "exists_polynomialDecoder_of_card_le", "exists_cyclic_polynomialDecoder",
        "tame_polynomialDecoder_degree_iff",
    ),
}
NEW_MODULES = [("geometry", f"TRR08Geometry/{module}.lean",
                ["TRR08Geometry." + name for name in names])
               for module, names in NEW_REPORTS.items()]
MODULES = BASE.MODULES + NEW_MODULES

BOUNDARY = {
    "full_interpolation_theorem_formalized": False,
    "tame_short_model_interpolation_theorem_formalized": True,
    "actual_residue_eigenvector_exclusion_formalized": True,
    "main_theorem": "TRR08Geometry.tame_polynomialDecoder_degree_iff",
    "hypotheses": [
        "K is a field; W is an actual Mathlib smooth short Weierstrass curve.",
        "T has finite odd order N >= 19; the image of N in K is nonzero.",
        "The images of 2 and 3 in K are nonzero.",
        "u is any element of K; d is any natural number.",
    ],
    "conclusion": (
        "An actual polynomial D in K[X1,Y1,X2,Y2] with total degree at most d in each "
        "coordinate pair represents f_u(P+Q) on nonidentity subgroup inputs if and only if "
        "ceil(N/3) <= d."
    ),
    "derived_in_lean": [
        "The distinct x-roots have cardinality (N-1)/2.",
        "The actual residue sum is the leading coefficient of the odd Lagrange normal form.",
        "Every monomial of weight 2*a+3*b <= N-1 is annihilated.",
        "Actual block-bounded multivariate polynomials supply those moments when 3*d <= N-1.",
        "The assigned value at the identity contributes minus u times the residue.",
        "A bounded decoder forces the already excluded actual residue eigenvector.",
        "Cubic compression produces actual ordinary-degree point-mass polynomials.",
        "A finite tensor sum of those polynomials constructs every target matrix at degree ceil(N/3).",
    ],
    "remaining_obligations": [
        "Transfer generalized Weierstrass models to short form with degree preservation.",
        "Formalize the remaining function-field and divisor argument when the characteristic divides the marked order.",
        "Integrate the small-order integral certificates with the geometric interpolation theorem in Lean.",
    ],
    "model_limits": [
        "This theorem concerns ordinary total degree in each affine coordinate pair on S times S.",
        "It supplies no general circuit, discrete-logarithm or signature-security lower bound.",
    ],
}


def reject_changed_theorem(lake: str, geometry: Path, logs: Path,
                           module: str, theorem: str, following: str,
                           old: str, new: str, name: str) -> dict:
    source = geometry / "TRR08Geometry" / (module + ".lean")
    original = source.read_text()
    start_match = re.search(r"\btheorem " + re.escape(theorem) + r"\b", original)
    if start_match is None:
        raise ValueError(f"The mathematical mutation theorem is missing: {name}")
    start = start_match.start()
    end_match = re.search(r"\ntheorem " + re.escape(following) + r"\b", original[start:])
    if end_match is None:
        raise ValueError(f"The mathematical mutation boundary is missing: {name}")
    end = start + end_match.start()
    segment = original[start:end]
    if segment.count(old) != 1:
        raise ValueError(f"The mathematical mutation target has changed: {name}")
    modified = original[:start] + segment.replace(old, new, 1) + original[end:]
    first_line = original[:start].count("\n") + 1
    last_line = original[:end].count("\n") + 1
    with tempfile.TemporaryDirectory(prefix="trr10-lean-control-") as directory:
        bad = Path(directory) / (module + "Changed.lean")
        bad.write_text(modified)
        began = time.monotonic()
        result = subprocess.run([lake, "env", "lean", str(bad)], cwd=geometry,
                                capture_output=True, text=True, timeout=180)
        output = result.stdout + result.stderr
        (logs / (name + ".log")).write_text(output)
        if result.returncode == 0 or "error" not in output:
            raise ValueError(f"Lean failed to reject the changed conclusion: {name}")
        if any(term in output for term in ("unknown module prefix", "object file", "No such file")):
            raise ValueError(f"The mutation control failed before its mathematical proof: {name}")
        error_lines = [int(line) for line in re.findall(
            re.escape(bad.name) + r":(\d+):\d+: error\b", output)]
        if not any(first_line <= line <= last_line for line in error_lines):
            raise ValueError(f"The mutation was rejected outside the changed theorem: {name}")
        return {"name": name, "status": "rejected", "compiler_exit_code": result.returncode,
                "source_sha256": CORE.sha256(source), "mutated_sha256": CORE.sha256(bad),
                "changed_theorem_line_interval": [first_line, last_line],
                "compiler_error_lines": error_lines,
                "elapsed_seconds": round(time.monotonic() - began, 6)}


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
    receipt = {"schema": "trr10-formalization-v1", "status": "running",
               "checked_at_utc": datetime.now(timezone.utc).isoformat(),
               "proof_boundary": BOUNDARY, "modules": []}
    start = time.monotonic()
    try:
        version = CORE.run([args.lake, "env", "lean", "--version"], core,
                           logs / "lean-version.log", 30).stdout.strip()
        if "version 4.35.0" not in version:
            raise ValueError(f"Unexpected Lean version: {version}")
        geometry_version = CORE.run([args.lake, "env", "lean", "--version"], geometry,
                                    logs / "geometry-lean-version.log", 30).stdout.strip()
        if geometry_version != version:
            raise ValueError(f"Geometry Lean version differs from the core: {geometry_version}")
        manifest = json.loads((geometry / "lake-manifest.json").read_text())
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        installed = subprocess.check_output(["git", "rev-parse", "HEAD"],
                    cwd=geometry / ".lake/packages/mathlib", text=True).strip()
        if mathlib["rev"] != CORE.PINNED_MATHLIB or installed != CORE.PINNED_MATHLIB:
            raise ValueError("Mathlib differs from the reviewed revision")
        receipt.update({"lean_version": version, "geometry_lean_version": geometry_version,
            "mathlib_revision": installed,
            "geometry_manifest_sha256": CORE.sha256(geometry / "lake-manifest.json"),
            "verifier_sha256": CORE.sha256(Path(__file__)),
            "trr09_verifier_sha256": CORE.sha256(BASE_PATH),
            "trr08_verifier_sha256": CORE.sha256(BASE.BASE_PATH)})
        CORE.run([args.lake, "build", "MathCan.TranslationInterpolationUniform",
                  "MathCan.TranslationInterpolationRootBound", "MathCan.TranslationInterpolationEvaluation"],
                 core, logs / "core-build.log", 600)
        CORE.run([args.lake, "build", "TRR08Geometry"], geometry, logs / "geometry-build.log", 1200)
        roots = {"core": core, "geometry": geometry}
        all_expected = [name for _, _, names in MODULES for name in names]
        if len(all_expected) != len(set(all_expected)) or len(all_expected) != 180:
            raise ValueError("The 113 plus 67 declaration contract has changed")
        for group, relative, expected in MODULES:
            source = roots[group] / relative
            code = source.read_text()
            BASE.guard_source(code, relative)
            BASE.source_report_contract(code, relative, expected)
            result = CORE.run([args.lake, "env", "lean", relative], roots[group],
                              logs / (source.stem + ".log"), 300)
            reports = CORE.parse_reports(result.stdout, expected)
            receipt["modules"].append({"project": group, "path": relative,
                "source_sha256": CORE.sha256(source), "principal_report_count": len(reports),
                "transitive_axioms": reports})
        receipt["principal_report_count"] = len(all_expected)
        receipt["new_principal_report_count"] = sum(len(names) for _, _, names in NEW_MODULES)
        receipt["mathematical_mutation_controls"] = [
            BASE.reject_wrong_residue_identity(args.lake, geometry, logs),
            reject_changed_theorem(args.lake, geometry, logs, "ResidueMonomials",
                "residueSum_monomial_eq_zero", "sum_residue_monomial_eq_zero",
                "(hweight : 2*a + 3*b ≤ Fintype.card H - 1)",
                "(hweight : 2*a + 3*b ≤ Fintype.card H)",
                "reject-one-higher-residue-weight"),
            reject_changed_theorem(args.lake, geometry, logs, "TameDecoder",
                "assignedX_residue_row", "polynomialDecoder_eigenvector_of_moments",
                "residueMatrixRow H P - u * subgroupResidue H P := by",
                "residueMatrixRow H P + u * subgroupResidue H P := by",
                "reject-assigned-value-sign"),
        ]
        receipt["status"] = "passed"
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError, StopIteration) as exc:
        receipt["status"] = "failed"
        receipt["error"] = str(exc)
    receipt["elapsed_seconds"] = round(time.monotonic() - start, 6)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": receipt["status"], "receipt": str(output),
                     "principal_reports": receipt.get("principal_report_count"),
                     "new_principal_reports": receipt.get("new_principal_report_count"),
                     "tame_short_model_interpolation_theorem_formalized": True}), flush=True)
    return 0 if receipt["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
