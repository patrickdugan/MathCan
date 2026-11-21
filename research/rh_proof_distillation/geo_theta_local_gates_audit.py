"""RHD-06: source-pinned local place and theta weight gate audit.

The modular witness checks necessary local compatibility only. It does
not reconstruct the upstream number-field primes or full Galois row.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = "f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3"
SOURCES = {
    "apart": ("src/Development/AbelianVarietyTheory/Statements/EllipticCurveLevels/ClosedAtLConclusionOfMem.lean", "965f8edd497289186739a8086a6f656e0c512dea"),
    "oneK": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/HodgeTrAt.lean", "604ffa570273fb3b322d4418da2248f8f35cdffd"),
    "sameK": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/ZetaCharacterDivisibility/StConj.lean", "c6d2d78210bdfb03e062f4b9d1a84413a7914597"),
    "seed": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/ZetaCharacterDivisibility/SeedFinOddOf.lean", "085613b42b9d49c8b79aae4a4ebbaec019b9a9fd"),
    "sameOr": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/ZetaCharacterDivisibility/PSameOr.lean", "7d00c8fbe7cb754671982ec731549be9c3d2b742"),
    "theta": ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/GalTPDefs.lean", "42831f56b9baacfaca0cde1207a1337882556e4c"),
}
REQUIRED = {
    "apart": (
        "def Apart (w u : HeightOneSpectrum (𝓞 E)) : Prop :=",
        "w.under (𝓞 (maximalRealSubfield E)) ≠ u.under (𝓞 (maximalRealSubfield E))",
    ),
    "oneK": (
        "def OneK (x : E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :=",
        "IntermediateField.adjoin ℚ {x}",
    ),
    "sameK": (
        "def SameK (x : E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :=",
        "IntermediateField.adjoin ℚ {x}",
    ),
    "seed": (
        "theorem seedFinOdd_of",
        "hG E Ω l ι a hodd d hd x hx T hT u₀ u'",
        "fun y hy => (a2 y hy).trans (b2 y hy).symm",
    ),
    "sameOr": (
        "theorem UpperTheory.Gal.Int.Div.sameOr_of",
        "SameOr := by",
        "hKc",
    ),
    "theta": (
        "def TLift_k : Prop :=",
        "∃ d₀ : ℕ, ∀ d, d₀ ≤ d",
        "(∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k)",
        "∃ U' : Submodule",
    ),
}


def blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def quadratic_agreement(source: str, name: str) -> str:
    header = f"def {name} (x : E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :="
    if source.count(header) != 1:
        raise ValueError(f"missing or duplicated declaration: {name}")
    body = source.split(header, 1)[1].strip().splitlines()[0].strip()
    return " ".join(body.split())


def source_contract(label: str, source: str) -> int:
    absent = [k for k in REQUIRED[label] if k not in source]
    if absent:
        raise ValueError(f"{label}: missing source anchors: {absent}")
    if label == "theta":
        a = source.index("∃ d₀ : ℕ, ∀ d, d₀ ≤ d")
        b = source.index("(∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k)")
        c = source.index("∃ U' : Submodule", b)
        if not a < b < c:
            raise ValueError("theta gate quantifiers or conclusion reordered")
    return len(REQUIRED[label])


def _multiply_integral_basis(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    """Multiplication in Z[i,phi], i^2=-1 and phi^2=phi+1.

    The basis index is (i exponent) + 2*(phi exponent).
    """
    out = [0, 0, 0, 0]
    for ia, ca in enumerate(a):
        for ib, cb in enumerate(b):
            ipow = ia % 2 + ib % 2
            ppow = ia // 2 + ib // 2
            coefficient = ca * cb * (-1 if ipow == 2 else 1)
            idx = ipow % 2
            if ppow == 0:
                out[idx] += coefficient
            elif ppow == 1:
                out[2 + idx] += coefficient
            else:
                out[idx] += coefficient
                out[2 + idx] += coefficient
    return tuple(out)


def _eval_integral_basis(coeffs: tuple[int, ...], u: int, t: int, p: int) -> int:
    """Evaluate a + b*i + c*phi + d*i*phi in the residue field."""
    return (coeffs[0] + coeffs[1] * u + coeffs[2] * t + coeffs[3] * u * t) % p


def residue_model(p: int = 29) -> dict:
    if p != 29:
        raise ValueError("only the documented p=29 witness is certified")
    roots_i = [u for u in range(p) if (u * u + 1) % p == 0]
    roots_f = [v for v in range(p) if (v * v - 5) % p == 0]
    roots_phi = [v for v in range(p) if (v * v - v - 1) % p == 0]
    if roots_i != [12, 17] or roots_f != [11, 18] or roots_phi != [6, 24]:
        raise ValueError("residue roots mismatch")
    a, b = (12, 11), (12, 18)
    assert a[0] == b[0] and a[1] != b[1]
    assert all((u * u + 1) % p == 0 and (v * v - 5) % p == 0 for u, v in [a, b])
    basis = [tuple(int(j == i) for j in range(4)) for i in range(4)]
    pairs = [(12, 6), (12, 24)]
    for u, phi in pairs:
        for left in basis:
            for right in basis:
                actual = _eval_integral_basis(_multiply_integral_basis(left, right), u, phi, p)
                expected = (_eval_integral_basis(left, u, phi, p) *
                            _eval_integral_basis(right, u, phi, p)) % p
                if actual != expected:
                    raise ValueError("integral basis evaluation is not multiplicative")
    return {
        "prime": p,
        "imaginary_roots": roots_i,
        "real_roots": roots_f,
        "phi_roots": roots_phi,
        "pair": [list(a), list(b)],
        "same_imaginary_reduction": True,
        "distinct_real_reduction": True,
        "integral_basis": ["1", "i", "phi", "i*phi"],
        "basis_relation": "i^2=-1, phi^2=phi+1",
        "evaluation_pairs_i_phi": [list(t) for t in pairs],
        "basis_product_hom_checks": 32,
        "prime_ideal_kernels": [
            "(29, i-12, phi-6)", "(29, i-12, phi-24)"
        ],
        "scope": ("modular arithmetic and 32 basis-product checks; "
                  "using the standard O_E = Z[i,phi] integral-basis fact; "
                  "no original Lean HeightOneSpectrum objects constructed"),
    }


def audit(upstream: Path) -> dict:
    head = subprocess.check_output(["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True).strip()
    if head != PIN:
        raise ValueError(f"upstream pin differs: {head}")
    text_map, receipts = {}, {}
    for label, (path, expected_blob) in SOURCES.items():
        raw = (upstream / path).read_bytes()
        actual = blob(raw)
        if actual != expected_blob:
            raise ValueError(f"{label}: source Git blob changed: {actual}")
        decoded = raw.decode("utf-8")
        count = source_contract(label, decoded)
        text_map[label] = decoded
        receipts[label] = {
            "path": path,
            "git_blob": actual,
            "sha256": hashlib.sha256(raw).hexdigest(),
            "anchors_checked": count,
        }
    one = quadratic_agreement(text_map["oneK"], "OneK")
    same = quadratic_agreement(text_map["sameK"], "SameK")
    if one != same:
        raise ValueError("OneK / SameK quadratic-place definitions differ")
    return {
        "schema_version": 1,
        "upstream_commit": PIN,
        "proof_term_data": False,
        "sources": receipts,
        "oneK_sameK_body_equal": True,
        "oneK_sameK_body_sha256": hashlib.sha256(one.encode()).hexdigest(),
        "apart_definition": "distinct restrictions to ring of integers of maximal real subfield",
        "residue_model": residue_model(),
        "theta_weight_gate": "for every w,k: (d:Int) + mW(w) <= 2*lambda(w,k)",
        "limits": [
            "Mod-29 roots establish local compatibility, not full FieldOK, PlanEx or GeoOne",
            "No actual height-one prime ideals of O_E are constructed by this checker",
            "No admissible automorphic U is supplied",
            "A fixed character exponent and weight cannot meet dominance for all d",
            "Source definition equality is not imported Lean definitional-equality checking",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.upstream.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "sources": len(result["sources"]),
        "oneK_sameK_equal": result["oneK_sameK_body_equal"],
        "residue_model": result["residue_model"],
        "proof_term_data": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
