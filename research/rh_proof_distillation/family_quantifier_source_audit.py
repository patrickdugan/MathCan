"""Independent pinned-source quantifier-shape audit for RHD-02.

This reads only the exact upstream theorem statements and definition slices,
retains original byte provenance, and emits metadata. It does not import
upstream proofs or infer that any analytic hypothesis is true.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = "f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3"
DEFINITIONS = "src/Formalism/SharpRestriction/GlobalSchurBounds/ZetaZeroFreeRegion.lean"
THEOREMS = "src/Formalism/SharpRestriction/GlobalSchurBounds/RamificationTwoAndConjugationAtQAndD.lean"
BLOBS = {
    DEFINITIONS: "7746e5a5affe67117d4ba907dbcd2788f539db6e",
    THEOREMS: "1c1495ef81c77fa96f3c1a70106c1da9e24c0c5d",
}
GATES = {
    "AllLargeC": ("def AllLargeC ", [
        "∃ C x0 : ℝ", "0 < C", "1 < x0",
        "∀ x : ℝ, x0 ≤ x → ∀ i : (Fm ε h0 h1).Ix x,",
    ]),
    "AllLargeAt": ("def AllLargeAt ", [
        "∃ x0 : ℝ", "1 < x0",
        "∀ x : ℝ, x0 ≤ x → ∃ i : (Fm ε h0 h1).Ix x,",
    ]),
    "SizesFe": ("def SizesFe ", [
        "∀ δ : ℝ, 0 < δ → ∃ x0 : ℝ", "SizesAt ", "PlacesAt ",
    ]),
    "FamilyPropTwoSix": ("def FamilyPropTwoSix ", ["AllLargeC Fm ε0 adm5"]),
    "FamilyCharacterSumBounds": ("def FamilyCharacterSumBounds ", ["AllLargeC Fm ε0 adm6"]),
    "TOPF": ("def TOPF ", ["AllLargeAt Fm ε0 adm7 C"]),
}
FAMILY_BRIDGE = (
    "theorem proposition_eleven_two_along_family ",
    ("adm5 ", "adm6 ", "SizesAt ", "PlacesAt ", "adm7 ",
     "proposition_eleven_two_at_scale", "∃ i : Fm.Ix x,"),
)


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\x00" + raw).hexdigest()


def declaration_slice(text: str, token: str) -> tuple[int, str]:
    pos = text.find(token)
    if pos < 0:
        raise ValueError("declaration not found: " + token)
    # Capture exactly the declaration until the next newline-led
    # top-level source declaration; this is only a syntactic slice.
    rest = text[pos:]
    candidates = [
        idx for key in ("\ndef ", "\ntheorem ", "\nlemma ", "\nstructure ")
        if (idx := rest.find(key, len(token))) >= 0
    ]
    stop = min(candidates) if candidates else len(rest)
    return text.count("\n", 0, pos) + 1, rest[:stop]


def inspect_text(definitions: str, theorems: str) -> dict:
    sites = {}
    for symbol, (marker, required) in GATES.items():
        line, source = declaration_slice(definitions, marker)
        absent = [needle for needle in required if needle not in source]
        if absent:
            raise ValueError(f"{symbol} missing source clauses: {absent}")
        sites[symbol] = {"path": DEFINITIONS, "line": line,
                         "text_sha256": hashlib.sha256(source.encode()).hexdigest(),
                         "required_fragments": required,
                         "evidence": "source_statement_text"}
    marker, required = FAMILY_BRIDGE
    line, body = declaration_slice(theorems, marker)
    absent = [needle for needle in required if needle not in body]
    if absent:
        raise ValueError(f"family bridge missing source clauses: {absent}")
    sites["proposition_eleven_two_along_family"] = {
        "path": THEOREMS, "line": line,
        "text_sha256": hashlib.sha256(body.encode()).hexdigest(),
        "required_fragments": list(required), "evidence": "source_statement_and_body_text",
    }
    return sites


def audit(root: Path) -> dict:
    head = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD"], text=True
    ).strip()
    if head != PIN:
        raise ValueError("source checkout is not at the pinned commit")
    contents = {}
    for path, expected in BLOBS.items():
        raw = (root / path).read_bytes()
        if git_blob(raw) != expected:
            raise ValueError("source Git blob does not match: " + path)
        contents[path] = raw.decode("utf-8")
    return {
        "source_commit": PIN, "source_blobs": BLOBS,
        "sites": inspect_text(contents[DEFINITIONS], contents[THEOREMS]),
        "proof_term_data": False, "verified_by": "pinned source text and Git blobs",
        "limitations": (
            "This source audit checks quantifier order and named calls, "
            "not truth, nonvacuity of every premise, or kernel proof dependencies."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    report = audit(args.upstream.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "source_commit": PIN, "verified_blobs": len(BLOBS),
        "quantifier_gates": len(report["sites"]), "proof_term_data": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
