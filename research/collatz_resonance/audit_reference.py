"""Replay the recovered 137-cycle reference and verify its arithmetic labels.

Run as python -m research.collatz_resonance.audit_reference. Pass complete
CSV outputs from both C++ algorithms to certify the enumeration comparison.
"""
import argparse
import csv
import hashlib
import json
from collections import Counter, defaultdict
from itertools import combinations
from math import gcd, prod
from pathlib import Path

from .arithmetic import BranchLattice, construct_sign_parameters, near_resonances, primitive_prime_lattice
from .collatz_core import full_step, odd_step

D = 160_833_217
PRIMES = (29, 53, 269, 389)
FIELDS = ("cycle_minimum", "odd_steps", "halvings", "triple_branches", "gcd_with_d")
BASE = Path(__file__).parent


def read_rows(path: Path) -> list[tuple[int, ...]]:
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream)
        if tuple(reader.fieldnames or ()) != FIELDS:
            raise ValueError("unexpected census columns")
        rows = [tuple(int(row[name]) for name in FIELDS) for row in reader]
    if len({row[0] for row in rows}) != len(rows):
        raise ValueError("duplicate cycle minima")
    return sorted(rows)


def log_tables() -> list[dict[int, int]]:
    result = []
    for p in PRIMES:
        table, x = {}, 1
        for exponent in range(p-1):
            if x in table:
                raise AssertionError("2 does not generate a local unit group")
            table[x] = exponent
            x = 2*x % p
        result.append(table)
    return result


def orbit_label(n: int, tables: list[dict[int, int]], logs: tuple[int, ...]) -> tuple:
    support = tuple(i for i, p in enumerate(PRIMES) if n % p)
    if not support:
        return (), ()
    first = support[0]
    exponents = tuple((tables[i][n % PRIMES[i]] - tables[first][n % PRIMES[first]]) % 4
                      for i in support[1:])
    shift = tuple((logs[i]-logs[first]) % 4 for i in support[1:])
    translated = tuple((e+s) % 4 for e, s in zip(exponents, shift))
    return support, min(exponents, translated)


def relative_sign_label(n: int) -> tuple[int, ...]:
    signs = tuple(0 if n % p == 0 else (1 if pow(n, (p-1)//2, p) == 1 else -1) for p in PRIMES)
    return min(signs, tuple(-x for x in signs))


def replay_cycle(row: tuple[int, ...]) -> int:
    minimum, r, A, u, g = row
    n = minimum
    seen = set()
    count_A = count_u = 0
    while n not in seen:
        if n % 2 != 1 or n > D or gcd(n, D) != g:
            raise AssertionError("invalid odd cycle vertex or gcd")
        seen.add(n)
        count_u += int(n % 4 == 1)
        n = full_step(n, D)
        while n % 2 == 0:
            n = full_step(n, D)
            count_A += 1
        if len(seen) > r or count_A > A:
            raise AssertionError("cycle exceeds declared length")
    if n != minimum or min(seen) != minimum or (len(seen), count_A, count_u) != (r, A, u):
        raise AssertionError("cycle replay disagrees with census")
    if A < 2*r or u > r or pow(2, A, D//g) != pow(3, u, D//g):
        raise AssertionError("branch-count constraint failed")
    return r+A


def run(path_csv: Path | None = None, peel_csv: Path | None = None) -> dict:
    reference = BASE / "data/reference_census.csv"
    rows = read_rows(reference)
    comparisons = {}
    for name, path in (("path", path_csv), ("peel", peel_csv)):
        if path is not None:
            if read_rows(path) != rows:
                raise AssertionError(f"{name} complete enumeration disagrees")
            comparisons[name] = {"rows_equal": True, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    periods = [replay_cycle(row) for row in rows]
    lattice, logs = primitive_prime_lattice(PRIMES)
    tables = log_tables()
    group_rows = []
    for zero_count in range(5):
        part = [row for row in rows if sum(row[0] % p == 0 for p in PRIMES) == zero_count]
        support_size = 4-zero_count
        predicted = 0
        if support_size == 0:
            predicted = 1
        else:
            for support in combinations(range(4), support_size):
                same = len({logs[i] % 4 for i in support}) == 1
                predicted += 4**(support_size-1) // (1 if same else 2)
        observed = len({orbit_label(row[0], tables, logs) for row in part})
        if predicted != observed:
            raise AssertionError("missing or conflicting modular orbit class")
        group_rows.append({"dividing_prime_factors": zero_count,
                           "relative_sign_classes": len({relative_sign_label(row[0]) for row in part}),
                           "periodic_classes": observed, "cycles": len(part)})
    family = defaultdict(list)
    by_minimum = {row[0]: row for row in rows}
    for minimum, r, A, u, g in rows:
        factors = tuple(p for p in PRIMES if (D//g) % p == 0)
        local = primitive_prime_lattice(factors)[0] if factors else BranchLattice(1, 1, 0, 1)
        if not local.contains(u, A):
            raise AssertionError("cycle outside reduced-modulus lattice")
        if g == 1:
            family[(u, A)].append(r+A)
    seeds = []
    for seed in (1, 5, 7, 11, 35, 55, 77, 385):
        n, positions, path = seed, {}, []
        while n not in positions:
            positions[n] = len(path)
            path.append(n)
            n = odd_step(n, D)[0]
        minimum = min(path[positions[n]:])
        row = by_minimum[minimum]
        seeds.append({"seed": seed, "cycle_minimum": minimum, "odd_steps": row[1],
                      "halvings": row[2], "triple_branches": row[3], "period": row[1]+row[2]})
    auxiliary = construct_sign_parameters((5, 7, 11))
    result = {"schema": "mathcan.collatz.audit.v1", "parameter": D,
              "odd_core_vertices": (D+1)//2, "cycles": len(rows),
              "periodic_integers": sum(periods), "maximum_period": max(periods),
              "full_unaccelerated_cycle_replays": len(rows),
              "complete_enumeration_comparisons": comparisons,
              "class_counts": group_rows,
              "unit_branch_families": [{"triple_branches": u, "halvings": A,
                   "cycles": len(v), "minimum_period": min(v), "maximum_period": max(v)}
                   for (u,A),v in sorted(family.items())],
              "lattice": {"triple_stride": lattice.triple_stride,
                          "halving_residue": lattice.halving_residue,
                          "halving_period": lattice.halving_period,
                          "index": lattice.index, "local_logs_of_3": logs,
                          "near_slope_six_u_le_10000_tolerance_100": near_resonances(lattice,10000,100)},
              "prescribed_seeds": seeds,
              "absolute_sign_construction": {"seed_primes": [5,7,11], "auxiliary_primes": auxiliary,
                                             "parameter": prod(auxiliary), "cycle_lower_bound": 27,
                                             "unit_cycle_lower_bound": 8},
              "reference_csv_sha256": hashlib.sha256(reference.read_bytes()).hexdigest(),
              "original_cpp_sha256": hashlib.sha256((BASE/'legacy/original_census.cpp').read_bytes()).hexdigest()}
    if (len(rows), sum(periods), max(periods)) != (137, 1869713, 74514):
        raise AssertionError("reference totals changed")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--path-csv", type=Path)
    parser.add_argument("--peel-csv", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.dumps(run(args.path_csv, args.peel_csv), indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(data)
    else:
        print(data, end="")
