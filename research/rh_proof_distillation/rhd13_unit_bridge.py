"""RHD-13: independent parity bridge for Lean finite-unit obstructions.

References merged RHD-10C (zeta20 / p29) and RHD-11 (zeta24 / p5).
The finite character annihilator is checked exhaustively and compared with
the eight constant vectors formalized in RHFiniteUnitObstructions.lean.
No global p-adic character or automorphic representation is constructed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from research.rh_proof_distillation.rhd10_unit_obstruction import (
    obstruction_receipt as zeta20_receipt,
)
from research.rh_proof_distillation.rhd11_crossfamily import (
    unit_obstruction as zeta24_receipt,
)

EXPECTED = {
    "zeta20_p29": {
        "p": 29,
        "vectors": (
            ((13, 14), (0, 28)),
            ((17, 23), (20, 3)),
            ((14, 23), (7, 3)),
            ((14, 14), (2, 28)),
        ),
        "determinants": (16, 26, 26, 16),
    },
    "zeta24_p5": {
        "p": 5,
        "vectors": (
            ((3, 0), (4, 4)),
            ((4, 2), (3, 0)),
            ((3, 0), (0, 2)),
            ((0, 4), (3, 0)),
        ),
        "determinants": (2, 4, 1, 3),
    },
}


def determinant(v: tuple[int, int], w: tuple[int, int], p: int) -> int:
    return (v[0]*w[1]-v[1]*w[0]) % p


def certify_pair(v: tuple[int, int], w: tuple[int, int], p: int) -> int:
    det = determinant(v, w, p)
    if det == 0:
        raise ValueError("two global unit vectors fail to span the local layer")
    # Independent from the determinant, exhaustively test every possible
    # nonzero additive character functional of the first layer.
    for a in range(p):
        for b in range(p):
            if a == 0 and b == 0:
                continue
            if (a*v[0]+b*v[1]) % p == 0 and (a*w[0]+b*w[1]) % p == 0:
                raise AssertionError("nonzero character kills both global units")
    return det


def normalized(name: str, original: dict) -> dict:
    expected = EXPECTED[name]
    p = expected["p"]
    observations = []
    places = original["places"]
    if len(places) != 4:
        raise AssertionError("expected four residue-degree-two places")
    for j, row in enumerate(places):
        actual = tuple(tuple(int(x) for x in v) for v in row["unit_log_vectors"])
        if actual != expected["vectors"][j]:
            raise AssertionError(f"{name} vector changed at place {j}")
        det = certify_pair(*actual, p)
        if det != expected["determinants"][j]:
            raise AssertionError(f"{name} determinant changed at place {j}")
        upstream = row[f"determinant_mod_{p}"]
        if det != upstream:
            raise AssertionError("unit obstruction report differs from finite verifier")
        observations.append({
            "factor_index": j,
            "vectors": [list(x) for x in actual],
            "determinant_mod_p": det,
            "nonzero_functionals_killing_both_units": 0,
        })
    if name == "zeta20_p29":
        norm_product = original["unit_norms_globally"]
        q_sum = original["local_character_sums_mod_29"]
    else:
        norm_product = original["global_norm_products_mod_25"]
        q_sum = original["character_exponent_sums_mod_5"]
    if norm_product != [1, 1] or q_sum != [0, 0]:
        raise AssertionError("global unit products fail")
    return {
        "source_family": name,
        "p": p,
        "unit_norm_products_mod_p2": norm_product,
        "dirichlet_exponent_sums_mod_p": q_sum,
        "places": observations,
    }


def report() -> dict:
    f29 = normalized("zeta20_p29", zeta20_receipt())
    f5 = normalized("zeta24_p5", zeta24_receipt())
    return {
        "experiment": "RHD-13 finite global-unit saturation bridge",
        "source_pins": ["RHD-10C", "RHD-11"],
        "finite_fields": [f29, f5],
        "kernel_expected_theorems": 8,
        "nonzero_linear_functionals_surviving": 0,
        "kernel_scope": "first-layer vector annihilator arithmetic only",
        "p_adic_global_witness_proved": False,
        "automorphic_witness_proved": False,
    }


def write_report(path: Path) -> dict:
    result = report()
    path.parent.mkdir(parents=True, exist_ok=True)
    content = (json.dumps(result, sort_keys=True, indent=2)+"\n").encode()
    path.write_bytes(content)
    path.with_suffix(".sha256").write_text(
        hashlib.sha256(content).hexdigest()+"  "+path.name+"\n")
    return result


if __name__=="__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(write_report(args.output), sort_keys=True, indent=2))
