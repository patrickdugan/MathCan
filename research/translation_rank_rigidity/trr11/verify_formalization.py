#!/usr/bin/env python3
"""Audit exact coordinate-block degree on generalized Weierstrass models."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
BASE_PATH = HERE.parent / "trr10" / "verify_formalization.py"
SPEC = importlib.util.spec_from_file_location("trr10_verifier", BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("Cannot load the TRR-10 verification contract")
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
V9 = BASE.BASE
CORE = BASE.CORE

# Reviewed declaration contract, independent of source text and compiler output.
NEW_REPORTS = {
    "AffinePolynomial": (
        "affineBivariateX_eval", "affineBivariateY_eval", "affineBivariateX_totalDegree",
        "affineBivariateY_totalDegree", "affineBivariateMonomial_eval",
        "affineBivariateMonomial_totalDegree", "affineBlockPullback_degree",
        "affineBlockPullback_eval", "BlockDegreeLE_add", "BlockDegreeLE_C",
        "affineBlockOutput_degree", "affineBlockOutput_eval",
    ),
    "GeneralCoordinates": (
        "shear_equation_iff", "shear_negY", "shear_inverse_pair_iff",
        "shear_addX", "shear_addY", "shear_slope",
    ),
    "ShortModelTransport": (
        "shearPointTo_from", "shearPointFrom_to", "shearPointTo_add",
        "shearPointEquiv_x", "shearPointEquiv_y", "toShortNF_unit",
        "shearModel_toShortNF", "shortPointEquiv_x", "shortPointEquiv_y",
    ),
    "DecoderTransport": (
        "assignedX_map_affine", "affineX_symm_of_addEquiv", "affineY_symm_of_addEquiv",
        "cyclicPointTransport_ne_zero", "decoderAffinePullback_degree",
        "polynomialDecoder_affine_pullback", "cyclic_polynomialDecoder_affine_iff",
    ),
    "GeneralDecoder": (
        "tame_general_polynomialDecoder_degree_iff",
        "tame_general_polynomialDecoder_degree_lower_bound",
        "tame_general_polynomialDecoder_at_minimum",
    ),
}
NEW_MODULES = [("geometry", f"TRR08Geometry/{module}.lean",
                ["TRR08Geometry." + name for name in names])
               for module, names in NEW_REPORTS.items()]
MODULES = BASE.MODULES + NEW_MODULES

BOUNDARY = {
    "full_interpolation_theorem_formalized": False,
    "tame_general_model_interpolation_theorem_formalized": True,
    "tame_short_model_interpolation_theorem_formalized": True,
    "generalized_coordinate_transfer_formalized": True,
    "actual_residue_eigenvector_exclusion_formalized": True,
    "main_theorem": "TRR08Geometry.tame_general_polynomialDecoder_degree_iff",
    "hypotheses": [
        "K is a field; W is an actual Mathlib smooth generalized Weierstrass curve.",
        "T has finite odd order N >= 19; the image of N in K is nonzero.",
        "The images of 2 and 3 in K are nonzero.",
        "u is any element of K; d is any natural number.",
    ],
    "conclusion": (
        "An actual polynomial D in K[X1,Y1,X2,Y2] with ordinary total degree at most d "
        "in each coordinate pair represents f_u(P+Q) on nonidentity subgroup inputs "
        "if and only if ceil(N/3) <= d."
    ),
    "derived_in_lean": [
        "The explicit shear carries the actual generalized curve equation to the changed model.",
        "Coordinate formulas preserve inverse pairs, secants, tangents and the actual point group law.",
        "The maps form an additive equivalence between actual curve point types.",
        "Mathlib's short normal form has unit scale one and is the specified shear model.",
        "Actual affine polynomial substitution preserves the ordinary degree bound in each block.",
        "The assigned identity value changes by the same x-translation as every finite output.",
        "Decoder existence is equivalent in both coordinate models with an explicit polynomial each way.",
        "The additive equivalence preserves marked order, allowing the complete tame short-model theorem to apply.",
    ],
    "remaining_obligations": [
        "Formalize the function-field and divisor argument for lower bounds when the characteristic divides the marked order.",
        "Integrate the small-order integral certificates with the geometric interpolation theorem in Lean.",
    ],
    "model_limits": [
        "The model is ordinary total degree in each affine coordinate pair on S times S.",
        "The degree theorem supplies no general circuit, discrete-logarithm or signature-security lower bound.",
    ],
}


def mathematical_controls(lake: str, geometry: Path, logs: Path) -> list[dict]:
    return [
        V9.reject_wrong_residue_identity(lake, geometry, logs),
        BASE.reject_changed_theorem(lake, geometry, logs, "ResidueMonomials",
            "residueSum_monomial_eq_zero", "sum_residue_monomial_eq_zero",
            "(hweight : 2*a + 3*b ≤ Fintype.card H - 1)",
            "(hweight : 2*a + 3*b ≤ Fintype.card H)",
            "reject-one-higher-residue-weight"),
        BASE.reject_changed_theorem(lake, geometry, logs, "TameDecoder",
            "assignedX_residue_row", "polynomialDecoder_eigenvector_of_moments",
            "residueMatrixRow H P - u * subgroupResidue H P := by",
            "residueMatrixRow H P + u * subgroupResidue H P := by",
            "reject-assigned-value-sign"),
        BASE.reject_changed_theorem(lake, geometry, logs, "AffinePolynomial",
            "affineBlockPullback_eval", "BlockDegreeLE_add",
            "blockEval D (α*x₁+r)", "blockEval D (α*x₁-r)",
            "reject-affine-input-translation-sign"),
        BASE.reject_changed_theorem(lake, geometry, logs, "DecoderTransport",
            "assignedX_map_affine", "affineX_symm_of_addEquiv",
            "assignedX (u+r) (e P) =", "assignedX u (e P) =",
            "reject-unshifted-assigned-value"),
    ]


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
    receipt = {"schema": "trr11-formalization-v1", "status": "running",
               "checked_at_utc": datetime.now(timezone.utc).isoformat(),
               "proof_boundary": BOUNDARY, "modules": []}
    began = time.monotonic()
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
            "verifier_dependencies": {
                "trr10": CORE.sha256(BASE_PATH),
                "trr09": CORE.sha256(BASE.BASE_PATH),
                "trr08": CORE.sha256(V9.BASE_PATH),
            }})
        CORE.run([args.lake, "build", "MathCan.TranslationInterpolationUniform",
                  "MathCan.TranslationInterpolationRootBound", "MathCan.TranslationInterpolationEvaluation"],
                 core, logs / "core-build.log", 600)
        CORE.run([args.lake, "build", "TRR08Geometry"], geometry, logs / "geometry-build.log", 1200)
        roots = {"core": core, "geometry": geometry}
        expected_all = [name for _, _, names in MODULES for name in names]
        if len(expected_all) != len(set(expected_all)) or len(expected_all) != 217:
            raise ValueError("The 180 plus 37 declaration contract has changed")
        for group, relative, expected in MODULES:
            source = roots[group] / relative
            code = source.read_text()
            V9.guard_source(code, relative)
            V9.source_report_contract(code, relative, expected)
            result = CORE.run([args.lake, "env", "lean", relative], roots[group],
                              logs / (source.stem + ".log"), 300)
            reports = CORE.parse_reports(result.stdout, expected)
            receipt["modules"].append({"project": group, "path": relative,
                "source_sha256": CORE.sha256(source), "principal_report_count": len(reports),
                "transitive_axioms": reports})
        receipt["principal_report_count"] = len(expected_all)
        receipt["new_principal_report_count"] = sum(len(names) for _, _, names in NEW_MODULES)
        receipt["mathematical_mutation_controls"] = mathematical_controls(args.lake, geometry, logs)
        receipt["status"] = "passed"
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError, StopIteration) as exc:
        receipt["status"] = "failed"
        receipt["error"] = str(exc)
    receipt["elapsed_seconds"] = round(time.monotonic() - began, 6)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": receipt["status"], "receipt": str(output),
                     "principal_reports": receipt.get("principal_report_count"),
                     "new_principal_reports": receipt.get("new_principal_report_count"),
                     "tame_general_model_interpolation_theorem_formalized": True}), flush=True)
    return 0 if receipt["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
