"""RHD-03: pinned source audit of the live RH/GRH Main proof interface.

A source-text census of 195 literature wrapper theorems and direct proof
entrypoints. It does not extract elaborated Lean Expr dependencies; its source
and exact Git blob pins must agree with the archived upstream checkout.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = "f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3"
PATHS = {
    "main": ("src/Main.lean", "dbd5db70bc11b35f18fa5751216ab335321e7bfc"),
    "kernel": ("src/Supplements/Kernels/MainTheorems.lean", "6a542d7ce969a791fd12ce575f587e6bc29044bf"),
    "conclusion": ("src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean", "ee340012ab19713a8acfecf8adc6a331cbc2f1a4"),
    "row": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean", "f769999ac5e49241993e5efbf81e4d2cded18acd"),
    "window": ("src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean", "4cba179acd45ac08d3cad21f51c9b9d62715a9a4"),
    "literature": ("src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean", "a13ba1f8c38d4dbf2ddd809fbf9610a007936c24"),
    "zeta_bridge": ("src/Formalism/GammaFactorNonvanishing/CritLine.lean", "95fa4da5c50119db164aa93944d106f22fdb576d"),
}
CHECKS = {
    "main": ("theorem riemannHypothesis : RiemannHypothesis := rhOfAll",),
    "kernel": (
        "theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter",
        "theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi",
    ),
    "conclusion": (
        "UpperTheory.FinalTheorems.everyCharacter_of_row",
        "UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=",
        "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
    ),
    "row": ("galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK",),
    "window": (
        "automorphic_window_of_inputs",
        "OpenImageCondition.mk h",
        "baseChangeN h",
    ),
    "literature": (
        "every_character_of_literature_of_vWin",
        "every_character_of_theta_integrals_local_matching",
        "topCovolSlim2_use_alt_alt",
        "local_langlands_gl_recT_exists_of_literature",
    ),
    "zeta_bridge": ("theorem Formalism.VW.rh_of_every",),
}
OPEN_FIELDS = (
    "caraianiLocalGlobalDual",
    "localLanglandsExists",
    "galoisRepOfPolarizedPairLit",
)
WRAPPER = re.compile(r"theorem\s+UpperTheory\.LiteratureTheorems\.([^\s(:]+)")
QUALIFIED = re.compile(r"UpperTheory\.LiteratureTheorems\.([A-Za-z0-9_']+)")
DIRECT_FIELD = re.compile(r"\bO\.(caraianiLocalGlobalDual|localLanglandsExists|galoisRepOfPolarizedPairLit)\b")
O_USE = re.compile(r"\bO\b")


def git_blob_sha(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def verify_sources(root: Path) -> tuple[dict, dict]:
    head = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD"], text=True
    ).strip()
    if head != PIN:
        raise ValueError(f"upstream mirror commit mismatch: {head}")
    texts, evidence = {}, {}
    for key, (path, expected) in PATHS.items():
        raw = (root / path).read_bytes()
        actual = git_blob_sha(raw)
        if actual != expected:
            raise ValueError(f"{key} source blob differs: {actual}")
        body = raw.decode("utf-8")
        absent = [fragment for fragment in CHECKS[key] if fragment not in body]
        if absent:
            raise ValueError(f"{key} required source route missing: {absent}")
        texts[key] = body
        evidence[key] = {
            "path": path, "git_blob": actual,
            "sha256": hashlib.sha256(raw).hexdigest(),
            "bytes": len(raw),
        }
    return texts, {"head": head, "source_files": evidence}


def parse_open_fields(text: str) -> dict:
    start = text.find("structure UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop where")
    if start < 0:
        raise ValueError("pinned literature interface missing")
    next_theorem = text.find("\ntheorem ", start)
    if next_theorem < 0:
        raise ValueError("pinned literature interface is unterminated")
    block = text[start:next_theorem]
    result = {}
    for line in block.splitlines()[1:]:
        match = re.match(r"\s+(\w+)\s*:\s*(.*)", line)
        if match:
            result[match[1]] = match[2].strip()
    if set(result) != set(OPEN_FIELDS):
        raise ValueError(f"OpenLiteratureStatements fields changed: {sorted(result)}")
    if result["caraianiLocalGlobalDual"] != result["galoisRepOfPolarizedPairLit"]:
        raise ValueError("published duplicate Row propositions no longer coincide")
    if "RecTExists" not in result["localLanglandsExists"]:
        raise ValueError("local-Langlands field type changed")
    return result


def wrapper_graph(text: str) -> dict:
    starts = list(WRAPPER.finditer(text))
    if not starts:
        raise ValueError("source contains no literature wrapper declarations")
    nodes = {}
    for ix, match in enumerate(starts):
        name = match[1]
        block = text[match.start():(starts[ix + 1].start() if ix + 1 < len(starts) else len(text))]
        equals = block.find(":=")
        if equals < 0:
            raise ValueError(f"wrapper declaration missing body: {name}")
        header, value = block[:equals], block[equals + 2:]
        if not re.search(r"\bO\s*:", header):
            raise ValueError(f"wrapper lacks explicit O parameter: {name}")
        if name in nodes:
            raise ValueError("duplicate literature wrapper: " + name)
        nodes[name] = {
            "name": name, "line": text[:match.start()].count("\n") + 1,
            "body_text_uses_O": bool(O_USE.search(value)),
            "direct_fields": sorted(set(DIRECT_FIELD.findall(value))),
            "body_sha256": hashlib.sha256(value.encode()).hexdigest(),
            "body": value,
        }
    known = set(nodes)
    for name, info in nodes.items():
        info["wrapper_calls"] = sorted(
            {p for p in QUALIFIED.findall(info["body"]) if p in known and p != name}
        )
        del info["body"]
    root = "every_character_of_literature_of_vWin"
    if root not in nodes:
        raise ValueError("missing live EveryCharacter wrapper")
    visited, queue = set(), deque([root])
    edges = []
    while queue:
        name = queue.popleft()
        if name in visited:
            continue
        visited.add(name)
        for next_name in nodes[name]["wrapper_calls"]:
            edges.append({"caller": name, "callee": next_name})
            if next_name not in visited:
                queue.append(next_name)
    direct_users = {
        field: sorted(name for name, item in nodes.items() if field in item["direct_fields"])
        for field in OPEN_FIELDS
    }
    return {
        "root": root,
        "total_wrappers": len(nodes),
        "source_bodies_without_literal_O": sum(not v["body_text_uses_O"] for v in nodes.values()),
        "source_bodies_with_literal_O": sum(v["body_text_uses_O"] for v in nodes.values()),
        "reachable_wrapper_count": len(visited),
        "reachable_direct_call_edges": len(edges),
        "all_wrappers_reachable_from_root": len(visited) == len(nodes),
        "field_direct_users": direct_users,
        "nodes": [nodes[name] for name in sorted(nodes)],
        "edges": edges,
        "traversal_limited": False,
        "caveat": (
            "Lexical matches do not establish semantic independence from O, "
            "minimal proof dependencies, or actual kernel proof-term references."
        ),
    }


def audit(root: Path) -> dict:
    sources, identity = verify_sources(root)
    fields = parse_open_fields(sources["literature"])
    wrappers = wrapper_graph(sources["literature"])
    return {
        "schema_version": 1,
        "evidence": "exact upstream Git blobs and Lean source text",
        "proof_term_data": False,
        "upstream": identity,
        "root_source_chain": [
            {"theorem": "riemannHypothesis", "via": "rhOfAll"},
            {"theorem": "rhOfAll", "via": "Formalism.VW.rh_of_every allChi"},
            {"theorem": "allChi", "via": "UpperTheory.FinalTheorems.everyCharacter"},
            {"theorem": "UpperTheory.FinalTheorems.everyCharacter",
             "via": "UpperTheory.FinalTheorems.everyCharacter_of_row"},
            {"theorem": "UpperTheory.FinalTheorems.everyCharacter_of_row",
             "via": "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin"},
        ],
        "open_literature_fields": fields,
        "literature_wrappers": wrappers,
        "validity_limit": (
            "This is an original-source dependency map. It does not reprove "
            "the original GRH/RH theorem or independently check its published .olean artifacts."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    report = audit(args.source_root.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    w = report["literature_wrappers"]
    print(json.dumps({
        "source_pin": PIN, "source_files": len(report["upstream"]["source_files"]),
        "wrapper_count": w["total_wrappers"],
        "no_direct_O_mentions": w["source_bodies_without_literal_O"],
        "reached": w["reachable_wrapper_count"],
        "direct_field_uses": {k: len(v) for k, v in w["field_direct_users"].items()},
        "proof_term_data": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
