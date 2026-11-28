"""RHD-05: source-pinned geometric and theta-lift prerequisite contracts.

Checks source hashes, named supplier links, and the immediate proof-field
interfaces. This is NOT a Lean proof-term dependency graph or a proof of RH.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = "f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3"

SOURCES = {
    "steps": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/MapInvMul.lean", "5f0b07b831bbe8bf0dea7ce8a5e7378a28614f0b"),
    "ks_plan": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/PackExOf.lean", "760bbf58b01d01e4fbcea2f829564ab08e5bb621"),
    "steps_builder": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/StepsMain.lean", "741722ffb47f56ad88d06182644eb441d1b096b6"),
    "geometry": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean", "4af6c909184001b272f7bfc504eac4606dcda763"),
    "plan_builder": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/PrimeLevelLocalization/ExistsUnitaryGroupDatumOfVectorExponentSpectral.lean", "c9f1a910b54570f9658168301a6f37141c2796bf"),
    "plan_final": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/PrimeLevelLocalization/SpecTopHolds.lean", "8cf10d013812af3c28862907cfbf0d62847dd302"),
    "lefschetz_wrapper": ("src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LefschetzFixedPointFiniteEtaleCorrespondence.lean", "aac9adb87289e23b0695ccf0307535f9a9f91713"),
    "lefschetz_proof": ("src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/LefschetzFixedPointFiniteEtaleCorrespondence.lean", "e8dda5d174faa367dd7e786b98a5a68308efc83d"),
    "ks_hodge": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LefschetzSigmaSums/KsHodgeOfGeo.lean", "a7d61d0d4c186d70c262692c7344dacc013c7d83"),
    "theta_builder": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TPGTop.lean", "c1e81ba09c0e00fba45da9250509c36a72714bc1"),
    "theta_final": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TPGHolds.lean", "c621b46b313d554ed00af05fb0ab8eb4c5050c60"),
}

EXPECTED_FIELDS = {
    "steps": (
        "rep", "es", "crys", "jump", "phi", "cut", "twES", "twCrys",
        "twJ", "twPhi", "phiOf", "card", "jumpsOf", "rich",
        "char", "ss", "cont",
    ),
    "ks_plan": ("std", "ex", "nice", "good", "cong", "hodge"),
}

REQUIRED = {
    "steps": ("structure Steps : Prop where", "rep : RepEx", "cont : TP.Sub.ContLeft"),
    "ks_plan": (
        "def PlanEx : Prop :=", "Odd a →", "FieldOK E l d",
        "OneK x w₀ v'", "AutOffT T U", "SphOffU w₀ S U",
        "structure KSAll : Prop where", "hodge : KSHodge",
    ),
    "steps_builder": (
        "theorem steps_of (hC : CrysStep) (hJ : JumpStep) (hP : PhiStep) : Steps :=",
        "repEx_holds", "Mod.esStep_holds", "TP.Sub.contLeft_holds",
    ),
    "geometry": (
        "theorem weight_one_geometric_realization : LocalSmoothExtension.HolomorphicLefschetzFormula",
        "exact GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence",
        "theorem geoOne_holds : GeoOne := geometric_realization_of_weight_one weight_one_geometric_realization",
    ),
    "plan_builder": (
        "theorem exists_unitaryGroupDatum_of_vector_exponent_spectral (h1 : VecEx) (h2 : ExpOf) (h3 : SpecTop) : PlanEx :=",
        "planEx_of ⟨frameEx_holds", "CertificateRingHomMap.rootsAlg_holds",
    ),
    "plan_final": (
        "theorem specTop_holds : SpecTop := UpperTheory.Gal.Spc.specTopG wtOf_holds",
        "theorem planEx_holds : PlanEx := exists_unitaryGroupDatum_of_vector_exponent_spectral vecEx_holds expOf_holds specTop_holds",
    ),
    "lefschetz_wrapper": (
        "theorem _root_.GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence",
        "UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence",
    ),
    "lefschetz_proof": (
        "theorem UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence",
        "exists_integral_clopen_decomposition_of_smooth",
        "holomorphic_lefschetz_finiteEtale_correspondence",
    ),
    "ks_hodge": (
        "theorem ksHodge_of_geo (hW : HolomorphicLefschetzFormula) (hF : FixK) : UpperTheory.Gal.Int.Geo.KSHodge :=",
        "ksHodge_of_inputs hW hF",
    ),
    "theta_builder": (
        "theorem tLift_of_tools_k", "_root_.UpperTheory.TP.tLift_of_k T hH",
        "_root_.UpperTheory.TP.nonVan_k T", "_root_.UpperTheory.TP.readLift_k T",
    ),
    "theta_final": (
        "theorem tools_holds_k", "theorem tLift_holds_k",
        "_root_.UpperTheory.TP.tLift_of_tools_k",
    ),
}


def blob_sha(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def proof_fields(source: str, name: str) -> tuple[str, ...]:
    marker = f"structure {name} : Prop where"
    if source.count(marker) != 1:
        raise ValueError(f"expected exactly one {marker}")
    body = source.split(marker, 1)[1]
    fields: list[str] = []
    for line in body.splitlines():
        m = re.match(r"^  ([a-zA-Z][a-zA-Z0-9]*)\s*:", line)
        if m:
            fields.append(m.group(1))
        elif line.strip():
            break
    return tuple(fields)


def verify_source(label: str, text: str) -> dict:
    missing = [s for s in REQUIRED[label] if s not in text]
    if missing:
        raise ValueError(f"{label} lost pinned supplier interface: {missing}")
    result = {"matched_anchors": len(REQUIRED[label])}
    if label == "steps":
        actual = proof_fields(text, "Steps")
        if actual != EXPECTED_FIELDS[label]:
            raise ValueError(f"Steps fields changed: {actual}")
        result["proof_fields"] = list(actual)
    if label == "ks_plan":
        actual = proof_fields(text, "KSAll")
        if actual != EXPECTED_FIELDS[label]:
            raise ValueError(f"KSAll fields changed: {actual}")
        result["proof_fields"] = list(actual)
    return result


def audit(upstream: Path) -> dict:
    head = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True
    ).strip()
    if head != PIN:
        raise ValueError(f"upstream changed: {head}")
    receipts = {}
    for label, (path, expected_sha) in SOURCES.items():
        raw = (upstream / path).read_bytes()
        got = blob_sha(raw)
        if got != expected_sha:
            raise ValueError(f"pinned source changed: {label}: {got}")
        checks = verify_source(label, raw.decode("utf-8"))
        receipts[label] = {
            "path": path, "git_blob": got, "sha256": hashlib.sha256(raw).hexdigest(),
            **checks,
        }
    return {
        "schema_version": 1,
        "mode": "pinned_source_geometric_and_theta_prerequisites",
        "upstream_commit": PIN,
        "proof_term_data": False,
        "sources": receipts,
        "immediate_inputs": {
            "GeoOne": ["Steps (17 fields)", "KSAll (6 fields)", "PlanEx"],
            "PlanEx": ["VecEx", "ExpOf", "SpecTop", "15-field planEx_of bundle"],
            "HolomorphicLefschetzFormula": ["finite-etale Lefschetz theorem"],
            "TLiftK": ["tLift_of_tools_k", "Tools_k", "HgtEx_k", "theta readLift/nonVan chain"],
        },
        "review_gates": [
            "Kernel axiom inventory on upstream GeoOne, TLiftK, row and Main declarations",
            "Compiled proof-term references for each imported mathematical supplier",
            "Concrete inhabitance/nonvacuity of PlanEx and TLiftK antecedents on row inputs",
            "Verify the actual row supplies all geometric and theta lift hypotheses",
        ],
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--upstream", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    report = audit(args.upstream.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "source_files": len(report["sources"]),
        "proof_term_data": False,
        "steps_fields": len(EXPECTED_FIELDS["steps"]),
        "ks_fields": len(EXPECTED_FIELDS["ks_plan"]),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
