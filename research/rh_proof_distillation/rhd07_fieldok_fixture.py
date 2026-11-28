"""RHD-07: source-pinned exact finite arithmetic fixtures for FieldOK/OneK.

The original field/ideal witnesses and automorphic inputs are NOT constructed
by this pure-Python tool. The arithmetical classification uses standard
cyclotomic factorization and the odd-prime Hensel square-root criterion.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = "f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3"
SOURCE = {
    "fieldok": (
        "src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/LatticeDataThicknessBound.lean",
        "740a7963b35640c34f75dddfe6fb5a0f33f60fa8", "def FieldOK"),
    "imq": (
        "src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/ApartAllEmpty.lean",
        "a1edf2e35538b69ebc063d64971c01247746eb16", "def SqAt"),
    "onek": (
        "src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/HodgeTrAt.lean",
        "604ffa570273fb3b322d4418da2248f8f35cdffd", "def OneK"),
    "seed": (
        "src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/ZetaCharacterDivisibility/SeedFinOddOf.lean",
        "085613b42b9d49c8b79aae4a4ebbaec019b9a9fd", "theorem seedFinOdd_of"),
    "dgen": (
        "src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/LimWPhi.lean",
        "c0dfe821f546e7a2016a32872f1511fa64f800b1", "def DGen"),
}


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\x00" + data).hexdigest()


def check_pinned_source(root: Path) -> dict:
    head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    if head != PIN:
        raise ValueError(f"upstream commit changed: {head}")
    result = {}
    for label, (path, expected, anchor) in SOURCE.items():
        raw = (root / path).read_bytes()
        if blob_sha(raw) != expected or anchor not in raw.decode("utf-8"):
            raise ValueError(f"source identity or declaration changed: {label}")
        result[label] = {"path": path, "blob": expected}
    return result


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    return all(n % k for k in range(2, int(n**0.5) + 1))


def legendre(a: int, p: int) -> int:
    return 0 if a % p == 0 else (1 if pow(a % p, (p - 1) // 2, p) == 1 else -1)


def poly_mul(a: tuple[int, ...], b: tuple[int, ...], p: int) -> tuple[int, ...]:
    v = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            v[i + j] = (v[i + j] + x * y) % p
    return tuple(v)


def factors_mod_prime(p: int) -> list[tuple[int, ...]]:
    """Irreducible monic factor coefficients ordered constant term first."""
    assert p > 3 and is_prime(p)
    if p % 12 == 1:
        roots = [r for r in range(p) if (r**4 - r**2 + 1) % p == 0]
        assert len(roots) == 4
        factors = [(-r % p, 1) for r in roots]
    elif p % 12 == 5:
        a = next(x for x in range(p) if x*x % p == p-1)
        factors = [(-1 % p, a, 1), (-1 % p, -a % p, 1)]
    elif p % 12 == 7:
        roots = [t for t in range(p) if (t*t + t + 1) % p == 0]
        assert len(roots) == 2
        factors = [(t, 0, 1) for t in roots]
    else:
        assert p % 12 == 11
        a = next(x for x in range(p) if x*x % p == 3 % p)
        factors = [(1, a, 1), (1, -a % p, 1)]
    factors.sort()
    product = (1,)
    for f in factors:
        product = poly_mul(product, f, p)
        if len(f) == 3:
            assert legendre(f[1] * f[1] - 4*f[0], p) == -1
    assert product == (1, 0, p-1, 0, 1)
    return factors


def classify(p: int, d: int) -> dict:
    assert d in (1, 3) and p > 3 and is_prime(p)
    factors = factors_mod_prime(p)
    local_square = legendre(-d, p) == 1
    relative_split = p % 12 != 11
    fieldok_arithmetic = local_square and relative_split
    pairs = []
    if p % 12 == 1:
        roots = sorted((-f[0]) % p for f in factors)
        k = 5 if d == 1 else 7
        pairs = sorted({tuple(sorted((r, pow(r, k, p)))) for r in roots})
        assert len(pairs) == 2 and all(a != b for a, b in pairs)
        for a, b in pairs:
            if d == 1:
                assert pow(a, 3, p) == pow(b, 3, p)
            else:
                assert (2*a*a - 1) % p == (2*b*b - 1) % p
    joint = fieldok_arithmetic and bool(pairs)
    assert joint == (p % 12 == 1)
    return {
        "ell": p, "ell_mod12": p % 12, "d": d,
        "factors_coefficients": [list(f) for f in factors],
        "rational_primes_in_E": len(factors),
        "ImQ": True, "SqAt_by_Hensel_unit": local_square,
        "even_real_degree": True, "everywhere_unramified_E_over_F": True,
        "all_places_above_ell_split_E_over_F": relative_split,
        "fieldok_arithmetic": fieldok_arithmetic,
        "oneK_and_apart_residue_pairs": [list(pair) for pair in pairs],
        "joint_arithmetic_gate": joint,
        "full_upstream_Lean_witness_constructed": False,
    }


def generate(limit: int = 1500) -> list[dict]:
    return [classify(p, d) for p in range(5, limit) if is_prime(p) for d in (1, 3)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    pinned = check_pinned_source(args.upstream.resolve()) if args.upstream else None
    rows = generate()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text("".join(json.dumps(x, sort_keys=True) + "\n" for x in rows))
    print(json.dumps({"source_files": len(pinned) if pinned else None,
                      "cases": len(rows), "fieldok_pass": sum(x["fieldok_arithmetic"] for x in rows),
                      "joint_pass": sum(x["joint_arithmetic_gate"] for x in rows),
                      "proof_term_data": False}, sort_keys=True))


if __name__ == "__main__":
    main()
