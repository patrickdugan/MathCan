"""RHD-04: source-attested inputs to the published Galois row theorem.

Compares the two source formulations of the theta lifting proposition,
and follows the named geometric/lift/recT witnesses to MainConclusion.
Statements are verified against the original, exact Git blob IDs.

This is source-text analysis, not full imported Lean proof-term closure.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = "f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3"
BASE = "src/Development/AutomorphicArithmetic/"
F = {
    "lift_type": ("Foundations/GaloisRepresentations/ThetaParseval/HalfIndexLattices/TLiftK.lean",
                  "4b36fc43e988270944cef2fc1b5e9ee1493fc275"),
    "lift_source": ("Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/GalTPDefs.lean",
                    "42831f56b9baacfaca0cde1207a1337882556e4c"),
    "lift_tools": ("Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TPGHolds.lean",
                   "c621b46b313d554ed00af05fb0ab8eb4c5050c60"),
    "lift_proved": ("Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean",
                    "e9101ee7d8551561a1d6ca3b18fdcfe84dbfc713"),
    "geo_parts": ("Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/GeoOneOfParts.lean",
                  "3954be7d48aae14c9c362152bdb3fffdb968fa05"),
    "geo_realization": ("Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/GeometricRealizationOfWeightOne.lean",
                        "a3966183e2d20f54fc7109a14dcf14979d89d8e1"),
    "geo_proved": ("Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean",
                   "4af6c909184001b272f7bfc504eac4606dcda763"),
    "row_core": ("Foundations/GaloisRepresentations/IntegralStructures/Development.lean",
                 "4d4d9506494734f28fce7d39bac1a50650ecf148"),
    "row_of_lift": ("Foundations/GaloisRepresentations/IntegralStructures/GaloisRepresentationsOfThetaLift.lean",
                    "869a5e68fcff90c1ee29a6dae75594ed8a59ada9"),
    "row_final": ("Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean",
                  "f769999ac5e49241993e5efbf81e4d2cded18acd"),
    "recT": ("Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean",
             "268786576f96cb5a2cea5fab2da4cf4f291c1116"),
    "conclusion": ("CharacterBoxes/MainConclusion.lean",
                   "ee340012ab19713a8acfecf8adc6a331cbc2f1a4"),
}
REQUIRED = {
    "lift_type": ("def TLiftK : Prop :=", "∃ d₀ : ℕ, ∀ d, d₀ ≤ d", "∃ U' :"),
    "lift_source": ("def TLift_k : Prop :=", "∃ d₀ : ℕ, ∀ d, d₀ ≤ d", "∃ U' :"),
    "lift_tools": ("theorem tools_holds_k", "theorem tLift_holds_k", "tLift_of_tools_k"),
    "lift_proved": ("theorem UpperTheory.TP.K.tLiftK", "UpperTheory.TP.tLift_holds_k"),
    "geo_parts": ("theorem geoOne_of_parts", "geoOne_of h₁ (packEx_of h₂ h₃)"),
    "geo_realization": ("theorem geometric_realization_of_weight_one", "steps_holds", "kodaira_spencer_of_weight_one", "Pl.planEx_holds"),
    "geo_proved": ("theorem geoOne_holds : GeoOne", "geometric_realization_of_weight_one weight_one_geometric_realization"),
    "row_core": ("theorem coreAll_of", "theorem galoisLocalGlobalStrong_of_geometry_lift", "UpperTheory.GalStar.Row0.row0b", "galoisLocalGlobal_of_geometry_lift geo up"),
    "row_of_lift": ("theorem galoisRepresentations_of_thetaLift", "galoisLocalGlobalStrong_of_geometry_lift UpperTheory.Gal.Int.Geo.geoOne_holds up"),
    "row_final": ("theorem galoisLocalGlobalStrong_recParameter", "galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK"),
    "recT": ("theorem UpperTheory.Zero.LLC.recTExists", "GlobalTheory.LocLanglands.exists_isLExt"),
    "conclusion": ("everyCharacter_of_row", "UpperTheory.Zero.LLC.recTExists", "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"),
}


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def definition_body(source: str, start: str) -> str:
    i = source.find(start)
    if i < 0:
        raise ValueError(f"missing Lean definition: {start}")
    rest = source[i + len(start):]
    # A namespace-free "end" at EOF is a valid terminator too.
    boundary = re.search(r"(?m)^[ \t]*(?:def|theorem|end|section)\b", rest)
    return rest[:boundary.start() if boundary else len(rest)].strip()

def normalize_lift_statement(statement: str) -> str:
    return " ".join(
        statement.replace("_root_.UpperTheory.TP.W.GoodK", "W.GoodK").split()
    )


def compare_lifts(a: str, b: str) -> dict:
    t1 = definition_body(a, "def TLiftK : Prop :=")
    t2 = definition_body(b, "def TLift_k : Prop :=")
    n1, n2 = normalize_lift_statement(t1), normalize_lift_statement(t2)
    if n1 != n2:
        raise ValueError("lift variants are not the same source proposition after normalization")
    if not all(needle in n1 for needle in (
        "∃ d₀ : ℕ, ∀ d, d₀ ≤ d",
        "W.IsSkew",
        "IsHecke",
        "HasExp",
        "∃ U' : Submodule",
    )):
        raise ValueError("pinned lifting statement lost quantified conditions")
    return {
        "canonical_statement_sha256": hashlib.sha256(n1.encode()).hexdigest(),
        "same_after_namespace_and_whitespace_normalization": True,
        "source_statement_bytes": [len(t1.encode()), len(t2.encode())],
        "scope": "source text; no definitional-equality kernel check",
        "quantifier_note": (
            "d0 is chosen before d, W, Hecke characters, weights and U, "
            "but after initial E/B/n/X and its hypotheses."
        ),
    }


def audit(root: Path) -> dict:
    head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"],
                                   text=True).strip()
    if head != PIN:
        raise ValueError(f"upstream revision mismatch: {head}")
    source, receipts = {}, {}
    for name, (relative, expected) in F.items():
        path = BASE + relative
        raw = (root / path).read_bytes()
        actual = git_blob(raw)
        if actual != expected:
            raise ValueError(f"original source blob changed for {name}")
        s = raw.decode("utf-8")
        absent = [x for x in REQUIRED[name] if x not in s]
        if absent:
            raise ValueError(f"source theorem links missing at {name}: {absent}")
        source[name] = s
        receipts[name] = {
            "source": path, "git_blob": actual, "sha256": hashlib.sha256(raw).hexdigest(),
            "bytes": len(raw),
        }
    lift = compare_lifts(source["lift_type"], source["lift_source"])
    return {
        "schema_version": 1,
        "mode": "pinned_source_theorem_input_graph",
        "upstream_commit": PIN,
        "proof_term_data": False,
        "verified_files": receipts,
        "theta_lift_equivalence": lift,
        "named_input_graph": [
            {"from": "UpperTheory.TP.K.tLiftK", "requires": "UpperTheory.TP.tLift_holds_k"},
            {"from": "UpperTheory.TP.tLift_holds_k", "requires": "UpperTheory.TP.tools_holds_k"},
            {"from": "UpperTheory.Gal.Int.Geo.geoOne_holds", "requires": "geometric_realization_of_weight_one"},
            {"from": "geometric_realization_of_weight_one", "requires": "Steps + KSAll + PlanEx"},
            {"from": "galoisRepresentations_of_thetaLift", "requires": "GeoOne + TLiftK"},
            {"from": "galoisLocalGlobalStrong_recParameter", "requires": "galoisRepresentations_of_thetaLift + tLiftK"},
            {"from": "UpperTheory.FinalTheorems.everyCharacter_of_row",
             "requires": "galoisLocalGlobalStrong_recParameter + recTExists + vwin_of_row"},
        ],
        "separate_local_langlands_proof": {
            "theorem": "UpperTheory.Zero.LLC.recTExists",
            "direct_source_calls": [
                "UpperTheory.Zero.LLC.artEx", "UpperTheory.Zero.LLC.cuspEx",
                "GlobalTheory.LocLanglands.exists_isLExt",
                "UpperTheory.Zero.LLC.extDim", "UpperTheory.Zero.LLC.extTw",
            ],
        },
        "limitations": [
            "These are named source statements and links, not full Lean proof-term references",
            "Identical normalized propositions are a source-text equality test, not a proof of Lean definitional equality",
            "The quantified theta-lifting and geometric input theorems remain unverified independently of the upstream published formalization",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    out = audit(args.upstream.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "upstream": PIN,
        "verified_files": len(out["verified_files"]),
        "lift_statements_equal": out["theta_lift_equivalence"]["same_after_namespace_and_whitespace_normalization"],
        "named_gates": len(out["named_input_graph"]),
        "proof_term_data": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
