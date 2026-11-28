"""RHD-08 exact cyclotomic Galois coset fibers.

These certificates instantiate finite groups and residue classes. They do not
construct number-field prime ideals or prove original upstream Lean propositions.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
from math import gcd
import json
from pathlib import Path

CONDUCTORS = (12, 15, 20, 21, 24, 28, 30, 36, 40, 44, 45, 48, 60, 84)


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def totient(n: int) -> int:
    return len(units(n))


@lru_cache(None)
def units(n: int) -> tuple[int, ...]:
    return tuple(k for k in range(1, n) if gcd(k, n) == 1)


@lru_cache(None)
def generated(n: int, x: int) -> tuple[int, ...]:
    if gcd(n, x) != 1:
        raise ValueError("need a unit modulo n")
    result = {1}
    y = 1
    while True:
        y = y * x % n
        if y in result:
            return tuple(sorted(result))
        result.add(y)


@lru_cache(None)
def kernel(n: int, d: int) -> tuple[int, ...]:
    if d not in (1, 3) or n % (4 if d == 1 else 3):
        raise ValueError("quadratic subfield absent")
    mod = 4 if d == 1 else 3
    return tuple(x for x in units(n) if x % mod == 1)


def cosets(n: int, group: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    rest = set(units(n))
    parts = []
    while rest:
        a = min(rest)
        c = tuple(sorted(a * g % n for g in group))
        if not set(c) <= rest:
            raise ValueError("not a subgroup")
        rest.difference_update(c)
        parts.append(c)
    return tuple(parts)


def conductor_cert(n: int) -> dict:
    if n not in CONDUCTORS:
        raise ValueError("uncertified conductor")
    order = n // gcd(n, 2)
    # All selected m have at least two distinct prime divisors, hence Φ_m(1)=1.
    distinct = {k for k in range(2, order + 1) if prime(k) and order % k == 0}
    return {"real_degree_even": (totient(n) // 2) % 2 == 0,
            "relative_derivative_unit": len(distinct) >= 2,
            "zeta_squared_order": order}


def classify(n: int, ell: int, d: int) -> dict:
    if not prime(ell) or gcd(n, ell) != 1:
        raise ValueError("prime must be unramified in cyclotomic E/Q")
    C = conductor_cert(n)
    G, H, D = units(n), kernel(n, d), generated(n, ell % n)
    HD = tuple(sorted({h * f % n for h in H for f in D}))
    upstairs = cosets(n, D)
    downstairs = cosets(n, HD)
    key = {x: j for j, c in enumerate(downstairs) for x in c}
    contraction = tuple(key[c[0]] for c in upstairs)
    same_pairs = tuple([a, b] for a, b in combinations(range(len(upstairs)), 2)
                       if contraction[a] == contraction[b])
    q = 4 if d == 1 else 3
    sq_at = ell % q == 1
    split_at_ell = (n - 1) not in D
    fieldok = all((sq_at, split_at_ell, C["real_degree_even"],
                   C["relative_derivative_unit"]))
    fiber = len(H) // len(set(H) & set(D))
    assert len(upstairs) * len(D) == len(G)
    assert len(downstairs) * fiber == len(upstairs)
    assert bool(same_pairs) == (fiber > 1)
    if sq_at:
        assert set(D) <= set(H)
        assert split_at_ell
    return {
        "n": n, "ell": ell, "d": d, "G_order": len(G), "H": list(H),
        "D": list(D), "HD": list(HD), "residue_degree": len(D),
        "E_prime_cosets": [list(c) for c in upstairs],
        "contraction_keys": list(contraction), "fiber_size": fiber,
        "SqAt": sq_at, "relative_split_at_ell": split_at_ell,
        "fieldok_arithmetic": fieldok, "oneK_distinct_pairs": list(same_pairs),
        "joint_arithmetic_gate": fieldok and bool(same_pairs),
        "upstream_Lean_witness_proved": False,
    }


def conductor_result(n: int, d: int) -> dict:
    H = kernel(n, d)
    orders = {g: len(generated(n, g)) for g in H}
    biggest = max(orders.values())
    gens = sorted(g for g, o in orders.items() if o == len(H))
    return {
        "n": n, "d": d, "H_order": len(H), "H_exponent": biggest,
        "minimum_prime_fiber_size": len(H) // biggest,
        "all_split_primes_have_OneK_pair": biggest < len(H),
        "counterexample_Frobenius_generator": gens[0] if gens else None,
        "proof_term_data": False,
    }


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--limit", type=int, default=500)
    args = p.parse_args()
    examples = []
    for n in CONDUCTORS:
        for d, m in ((1, 4), (3, 3)):
            if n % m:
                continue
            c = conductor_result(n, d)
            for ell in range(5, args.limit):
                if prime(ell) and gcd(n, ell) == 1:
                    examples.append({**classify(n, ell, d), "conductor": c})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w") as f:
        for example in examples:
            f.write(json.dumps(example, sort_keys=True) + "\n")
    print(json.dumps({"cases": len(examples),
                      "fieldok": sum(r["fieldok_arithmetic"] for r in examples),
                      "joint": sum(r["joint_arithmetic_gate"] for r in examples),
                      "proof_term_data": False}, sort_keys=True))


if __name__ == "__main__":
    main()
