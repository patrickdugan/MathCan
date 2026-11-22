"""RHD-14: exact local conjugation and norm-pullback descent obstruction.

Checks Q(zeta_20) at p=29 and Q(zeta_24) at p=5. The data show
that a base-field norm-pulled character has equal exponents on
complex-conjugate local factors. Its ratio on the norm-one torus
is zero, so it cannot produce a nontrivial rank-one local eigencharacter
*through this construction*. Actual original UA and TyEll remain
unimported and unproved.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from math import gcd
from pathlib import Path

from research.rh_proof_distillation.rhd09_local_character import (
    P as P29, lifted_factors as factors20,
    principal_norm as principal_norm20, dirichlet_exponent as q29,
    theta as trace29,
)
from research.rh_proof_distillation.rhd11_crossfamily import (
    P as P5, FACTORS as factors24,
    principal_norm as principal_norm24, q as q5,
    theta as trace5,
)


@dataclass(frozen=True)
class Family:
    label: str
    p: int
    factors: tuple[tuple[int, int, int], ...]
    q: object
    principal_norm: object
    trace: object


FAMILIES = (
    Family("Q(zeta_20)/p29", P29, factors20(), q29,
           principal_norm20, trace29),
    Family("Q(zeta_24)/p5", P5, factors24, q5,
           principal_norm24, trace5),
)


def conjugate_factor_indices(family: Family) -> tuple[int, ...]:
    """Reciprocal factors: f*(X)=X²+(c/d)X+1/d, since zeta maps to zeta^-1."""
    modulus = family.p**2
    pairs = []
    for d, c, _ in family.factors:
        options = [
            j for j, (d2, c2, _) in enumerate(family.factors)
            if (d*d2) % modulus == 1 and (c2*d) % modulus == c % modulus
        ]
        if len(options) != 1:
            raise AssertionError("complex conjugation has ambiguous reciprocal factor")
        pairs.append(options[0])
    return tuple(pairs)


def conjugate_coordinates(family: Family, index: int, a: int, b: int,
                          modulus: int | None = None) -> tuple[int, int]:
    """Under conjugation, zeta_j maps to alpha_k^-1=-(alpha_k+c_k)/d_k."""
    m = family.p**2 if modulus is None else modulus
    k = conjugate_factor_indices(family)[index]
    d_source = family.factors[index][0]
    c_target = family.factors[k][1]
    # Since d_source*d_target=1 mod p², -d_source is -1/d_target.
    return ((a-d_source*c_target*b) % m, (-d_source*b) % m)


def norm_in_quotient(f: tuple[int, int, int], a: int, b: int, m: int) -> int:
    return (a*a-f[1]*a*b+f[0]*b*b) % m


def first_layer_witness(family: Family, j: int, a: int, b: int) -> dict:
    k = conjugate_factor_indices(family)[j]
    fa, fb = conjugate_coordinates(family, j, a, b, family.p)
    local = family.trace(family.factors[j], a, b)
    conjugate = family.trace(family.factors[k], fa, fb)
    qlocal = family.q(family.principal_norm(family.factors[j], a, b))
    qconj = family.q(family.principal_norm(family.factors[k], fa, fb))
    if not (local == conjugate == qlocal == qconj):
        raise AssertionError("local character failed conjugation equivariance")
    return {
        "family": family.label,
        "p": family.p,
        "place": j,
        "conjugate_place": k,
        "a": a, "b": b,
        "conjugate_a": fa, "conjugate_b": fb,
        "local_norm_character": qlocal,
        "conjugate_norm_character": qconj,
        "norm_one_ratio_exponent": (qlocal-qconj) % family.p,
    }


def all_witnesses():
    for fam in FAMILIES:
        indices = conjugate_factor_indices(fam)
        if len(indices) != 4 or any(indices[indices[j]] != j for j in range(4)):
            raise AssertionError("conjugation failed to give four paired factors")
        if any(indices[j] == j for j in range(4)):
            raise AssertionError("expected no self-conjugate factor at a split place")
        for j in range(4):
            for a in range(fam.p):
                for b in range(fam.p):
                    yield first_layer_witness(fam, j, a, b)


def check_ring_conjugation(family: Family, samples: int = 2048) -> dict:
    """Independent nonlinear norm checks beyond the p-unit first layer."""
    modulus = family.p**2
    idx = conjugate_factor_indices(family)
    for j in range(4):
        d, c, _ = family.factors[j]
        d2, c2, _ = family.factors[idx[j]]
        if (d*d2) % modulus != 1 or (c2*d) % modulus != c % modulus:
            raise AssertionError("bad reciprocal Hensel-conjugate factor")
        for t in range(samples):
            digest = hashlib.sha256(
                f"RHD14/{family.label}/{j}/{t}".encode()
            ).digest()
            a = int.from_bytes(digest[:4], "big") % modulus
            b = int.from_bytes(digest[4:8], "big") % modulus
            x, y = conjugate_coordinates(family, j, a, b)
            n1 = norm_in_quotient(family.factors[j], a, b, modulus)
            n2 = norm_in_quotient(family.factors[idx[j]], x, y, modulus)
            if n1 != n2:
                raise AssertionError("full quadratic quotient norm changed")
            if gcd(n1, family.p) == 1 and family.q(n1) != family.q(n2):
                raise AssertionError("norm-pullback quotient mismatch")
    return {"sampled_pairs_per_factor": samples, "factors": 4,
            "checked_pairs": samples*4}


def receipt() -> dict:
    families = []
    count = 0
    for fam in FAMILIES:
        idx = conjugate_factor_indices(fam)
        unit_pairs = []
        for j in range(4):
            scalar = (fam.p+1)//2
            u = first_layer_witness(fam, j, scalar, 0)
            if u["local_norm_character"] != 1:
                raise AssertionError("source norm character is not locally nontrivial")
            if u["norm_one_ratio_exponent"] != 0:
                raise AssertionError("norm-one cancellation failed")
            unit_pairs.append(u)
        families.append({
            "field": fam.label,
            "p": fam.p,
            "conjugation_indices": list(idx),
            "local_nontrivial_symmetric_pairs": unit_pairs,
            "independent_full_ring_samples": check_ring_conjugation(fam),
            "first_layer_cases": 4*fam.p*fam.p,
        })
        count += 4*fam.p*fam.p
    rows = list(all_witnesses())
    if len(rows) != count or any(r["norm_one_ratio_exponent"] for r in rows):
        raise AssertionError("first-layer cancellation is incomplete")
    return {
        "experiment": "RHD-14 conjugation-invariant norm character and norm-one collapse",
        "families": families,
        "first_layer_cases": count,
        "all_norm_one_ratio_exponents_zero": True,
        "conditional_unitary_group_claim":
            "For U(1) as the E/F norm-one torus, any absolute-norm pullback is trivial.",
        "evidence_scope":
            "finite quadratic quotient identities, norm traces and source-type research",
        "original_TyEll_proved": False,
        "original_UA_identified_in_kernel": False,
    }


def write_data(output: Path) -> dict:
    output.parent.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    with output.with_suffix(".jsonl").open("wb") as stream:
        for row in all_witnesses():
            line = (json.dumps(row, sort_keys=True, separators=(",", ":"))+"\n").encode()
            stream.write(line)
            digest.update(line)
    result = receipt()
    result["jsonl_sha256"] = digest.hexdigest()
    data = (json.dumps(result, sort_keys=True, indent=2)+"\n").encode()
    output.write_bytes(data)
    output.with_suffix(".sha256").write_text(
        hashlib.sha256(data).hexdigest()+"  "+output.name+"\n"
    )
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(write_data(args.output), indent=2, sort_keys=True))
