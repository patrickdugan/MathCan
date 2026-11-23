"""RHD-17: exhaustive local ray-unit character modulo cyclotomic torsion.

R = (Z/p^2)[alpha]/(alpha^2+c alpha+d), with four unramified
degree-two Hensel factors for each Q(zeta20)/29 or Q(zeta24)/5.

Enumerates every element of all eight rings and verifies that the
norm-pulled exponent q(N(u)) distributes uniformly on R^x.
Primitive roots of unity alpha_j generate mu_n, lie in the kernel,
and act freely on R^x. Thus the character descends to R^x/mu_n
with exact index p.

This is an explicit finite local quotient, not T(A_F)/T(F), a Hecke
automorphic character, or the upstream TyEll proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

from research.rh_proof_distillation.rhd14_norm_one_collapse import FAMILIES

ORDERS = {29: 20, 5: 24}
PROPER_POWER_CHECKS = {29: (10, 4), 5: (12, 8)}


def multiply(f: tuple[int, int, int], x: tuple[int, int],
             y: tuple[int, int], m: int) -> tuple[int, int]:
    d, c, _ = f
    a, b = x
    v, w = y
    return ((a*v-d*b*w) % m, (a*w+b*v-c*b*w) % m)


def power(f: tuple[int, int, int], x: tuple[int, int],
          exponent: int, m: int) -> tuple[int, int]:
    if exponent < 0:
        raise ValueError("negative exponent")
    answer = (1, 0)
    while exponent:
        if exponent & 1:
            answer = multiply(f, answer, x, m)
        x = multiply(f, x, x, m)
        exponent >>= 1
    return answer


def norm(f: tuple[int, int, int], x: tuple[int, int], m: int) -> int:
    d, c, _ = f
    a, b = x
    return (a*a-c*a*b+d*b*b) % m


def exact_alpha_order(family, j: int) -> dict:
    f, p = family.factors[j], family.p
    m, n = p*p, ORDERS[p]
    if power(f, (0, 1), n, m) != (1, 0):
        raise AssertionError("cyclotomic root has wrong order")
    for proper in PROPER_POWER_CHECKS[p]:
        if power(f, (0, 1), proper, m) == (1, 0):
            raise AssertionError("cyclotomic root order is a proper divisor")
    values = []
    current = (1, 0)
    for k in range(n):
        if current in values:
            raise AssertionError("root repeated before its full order")
        values.append(current)
        current = multiply(f, current, (0, 1), m)
    if current != (1, 0) or len(set(values)) != n:
        raise AssertionError("root-subgroup orbit not exact")
    if any(family.q(norm(f, x, m)) != 0 for x in values):
        raise AssertionError("cyclotomic unit is not in character kernel")
    return {
        "factor": j, "root_order": n, "root_powers": len(values),
        "root_characters_all_zero": True,
    }


def normalized_witness(family, j: int) -> dict:
    p, m, f = family.p, family.p**2, family.factors[j]
    half = (p+1)//2
    u = ((1+p*half) % m, 0)
    val = family.q(norm(f, u, m))
    if val != 1:
        raise AssertionError("local order-p character not surjective")
    return {
        "u": list(u),
        "norm_mod_p2": norm(f, u, m),
        "character_exponent_mod_p": val,
    }


def deterministic_unit_orbits(family, j: int, samples: int = 128) -> int:
    p, m, n, f = family.p, family.p**2, ORDERS[family.p], family.factors[j]
    for i in range(samples):
        h = hashlib.sha256(f"RHD17/{p}/{j}/{i}".encode()).digest()
        a = int.from_bytes(h[:4], "big") % m
        b = int.from_bytes(h[4:8], "big") % m
        if (a % p, b % p) == (0, 0):
            a = (a+1) % m
        u = (a, b)
        if norm(f, u, m) % p == 0:
            raise AssertionError("nonzero residue pair was a nonunit")
        expected = family.q(norm(f, u, m))
        seen = set()
        cur = u
        for _ in range(n):
            if cur in seen:
                raise AssertionError("torsion orbit shorter than n")
            seen.add(cur)
            if family.q(norm(f, cur, m)) != expected:
                raise AssertionError("norm character varies on a root orbit")
            cur = multiply(f, cur, (0, 1), m)
        if cur != u or len(seen) != n:
            raise AssertionError("failed root-orbit closure")
    return samples


def exhaustive_unit_distribution(family, j: int) -> dict:
    p, m, n = family.p, family.p**2, ORDERS[family.p]
    f = family.factors[j]
    counts = [0] * p
    nonunits = 0
    for a in range(m):
        for b in range(m):
            nm = norm(f, (a, b), m)
            residue_unit = (a % p != 0 or b % p != 0)
            if residue_unit != (nm % p != 0):
                raise AssertionError("degree-two residue field property failed")
            if residue_unit:
                counts[family.q(nm)] += 1
            else:
                nonunits += 1
    ring_size = m*m
    unit_count = sum(counts)
    expected_units = p*p*(p*p-1)
    expected_each = p*(p*p-1)
    if nonunits != p*p or unit_count != expected_units:
        raise AssertionError("incorrect count of local units")
    if counts != [expected_each]*p:
        raise AssertionError("norm-character fibers not exactly uniform")
    if gcd(p, n) != 1 or unit_count % n != 0:
        raise AssertionError("torsion quotient unsupported")
    if any(c % n for c in counts):
        raise AssertionError("unit torsion does not divide character fibers")
    cosets = unit_count//n
    kernel_cosets = counts[0]//n
    if cosets//kernel_cosets != p or cosets != p*kernel_cosets:
        raise AssertionError("character became trivial on torsion quotient")
    return {
        "factor": j,
        "ring_size": ring_size,
        "nonunits": nonunits,
        "units": unit_count,
        "root_subgroup_order": n,
        "unit_char_histogram": counts,
        "kernel_units": counts[0],
        "root_quotient_cardinality": cosets,
        "root_quotient_kernel_cardinality": kernel_cosets,
        "root_quotient_character_order": p,
        "root_order_certificate": exact_alpha_order(family, j),
        "surjectivity_witness": normalized_witness(family, j),
        "root_orbits_sampled": deterministic_unit_orbits(family, j),
    }


def report() -> dict:
    families = []
    total_elements = 0
    for family in FAMILIES:
        result = [
            exhaustive_unit_distribution(family, j)
            for j in range(len(family.factors))
        ]
        total_elements += sum(row["ring_size"] for row in result)
        families.append({
            "field": family.label,
            "p": family.p,
            "cyclotomic_root_order": ORDERS[family.p],
            "first_layer_character_exponent_source": "q_p(N(u))",
            "factors": result,
        })
    return {
        "experiment": "RHD-17 local ray unit quotient by global cyclotomic torsion",
        "all_eight_factors_exhaustively_enumerated": True,
        "total_ring_elements_enumerated": total_elements,
        "families": families,
        "global_norm_one_torus_character_constructed": False,
        "upstream_TyEll_proved": False,
        "claim_scope": (
            "exact unramified degree-two finite local quotient R^x/mu_n; "
            "global adelic quotient and continuous character require separate proof"
        ),
    }


def write_report(output: Path) -> dict:
    result = report()
    output.parent.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(result, sort_keys=True, indent=2) + "\n").encode()
    output.write_bytes(data)
    output.with_suffix(".sha256").write_text(
        hashlib.sha256(data).hexdigest() + "  " + output.name + "\n"
    )
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = write_report(args.output)
    print(json.dumps({
        "enumerated": result["total_ring_elements_enumerated"],
        "factor_summary": [
            {"family": row["field"], "stats": [
                {"units": f["units"], "quotient": f["root_quotient_cardinality"],
                 "kernel": f["root_quotient_kernel_cardinality"]}
                for f in row["factors"]]}
            for row in result["families"]
        ],
    }, indent=2, sort_keys=True))
