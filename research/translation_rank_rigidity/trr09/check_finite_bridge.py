#!/usr/bin/env python3
"""Exact finite controls for the slope and residue identities in TRR-09."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
from itertools import combinations
import json
from pathlib import Path
import time


def curve_tables(p: int, A: int, B: int):
    points = [None] + [(x, y) for x in range(p) for y in range(p)
                       if (y*y - x*x*x - A*x - B) % p == 0]
    lookup = {P: i for i, P in enumerate(points)}
    size = len(points)
    add = [[0]*size for _ in points]
    slope = [[0]*size for _ in points]
    for i, P in enumerate(points):
        for j, Q in enumerate(points):
            if P is None:
                add[i][j] = j
                continue
            if Q is None:
                add[i][j] = i
                continue
            x, y = P
            v, w = Q
            if x == v and (y+w) % p == 0:
                continue
            m = ((w-y)*pow(v-x, -1, p) if x != v
                 else (3*x*x+A)*pow(2*y, -1, p)) % p
            z = (m*m-x-v) % p
            add[i][j] = lookup[z, (-y+m*(x-z)) % p]
            slope[i][j] = m
    neg = [0 if P is None else lookup[P[0], -P[1] % p] for P in points]
    return points, add, slope, neg


def verify(primes: list[int]):
    counts = Counter()
    by_prime = {}
    for p in primes:
        local = Counter()
        for A in range(p):
            for B in range(p):
                if (4*A**3+27*B**2) % p == 0:
                    continue
                points, add, slope, neg = curve_tables(p, A, B)
                size = len(points)
                local['smooth_models'] += 1
                for i in range(size):
                    for j in range(size):
                        ij = add[i][j]
                        for k in range(size):
                            jk = add[j][k]
                            assert add[ij][k] == add[i][jk], ('group law', p, A, B, i, j, k)
                            assert (slope[i][j]+slope[ij][k]-slope[j][k]-slope[i][jk]) % p == 0, (
                                'slope cocycle', p, A, B, i, j, k)
                            local['cocycle_triples'] += 1
                            if not i or not j or not k:
                                local['triples_with_identity'] += 1
                            if not ij or not jk:
                                local['triples_with_inverse_adjacent_pair'] += 1
                            if add[ij][k] == 0:
                                local['triples_with_zero_total'] += 1
                            if (i == j and ij != 0) or (j == k and jk != 0):
                                local['triples_with_nonvertical_tangent'] += 1
                seen = set()
                for generator in range(1, size):
                    sequence = [0]
                    current = generator
                    while current:
                        sequence.append(current)
                        current = add[current][generator]
                    subgroup = frozenset(sequence)
                    if subgroup in seen or len(subgroup) % 2 == 0:
                        continue
                    seen.add(subgroup)
                    N = len(subgroup)
                    local['odd_cyclic_subgroups'] += 1
                    if N % p == 0:
                        local['matching_characteristic_subgroups'] += 1
                    nonzero = sorted(subgroup - {0})
                    roots = sorted({points[i][0] for i in nonzero})
                    assert len(roots)*2 == N-1
                    deriv = {v: 1 for v in roots}
                    for v in roots:
                        for w in roots:
                            if v != w:
                                deriv[v] = deriv[v]*(v-w) % p
                    lam = {i: pow(2*points[i][1]*deriv[points[i][0]] % p, -1, p) for i in nonzero}
                    U = sum(points[i][0] for i in nonzero) % p
                    coeffs = {}
                    for i in nonzero:
                        x, y = points[i]
                        other = [v for v in roots if v != x]
                        invs = [pow(x-v, -1, p) for v in other]
                        S1 = sum(invs) % p
                        S2 = sum(a*b for a, b in combinations(invs, 2)) % p
                        tangent = slope[i][i]
                        coefficient = (-tangent-2*y*S1) % p
                        assert coefficient == -sum(slope[i][j] for j in subgroup) % p
                        coeffs[i] = coefficient
                        local['coefficient_pairing_checks'] += 1
                        weighted = deriv[x]*sum(pow((x-v)**2*deriv[v] % p, -1, p) for v in other) % p
                        assert weighted == (S2-S1*S1) % p
                        local['lagrange_second_coefficient_checks'] += 1
                        ratio = sum((0 if add[i][j] == 0 else points[add[i][j]][0])*lam[j]
                                    for j in nonzero)*pow(lam[i], -1, p) % p
                        expanded_b = (tangent*tangent-2*x+4*y*y*(S1*S1-S2)) % p
                        assert ratio == expanded_b
                        local['residue_ratio_checks'] += 1
                        assert (2*ratio-coefficient*coefficient+N*x) % p == U
                        local['constant_trace_checks'] += 1
                    for i in nonzero:
                        assert coeffs[add[i][i]] == (2*coeffs[i]+N*slope[i][i]) % p
                        local['doubling_checks'] += 1
        by_prime[str(p)] = dict(local)
        counts.update(local)
        print(f'Passed characteristic {p}: {local["smooth_models"]} models, '
              f'{local["cocycle_triples"]} triples, {local["odd_cyclic_subgroups"]} odd subgroups', flush=True)
    return dict(counts), by_prime


def main():
    if not __debug__:
        raise RuntimeError('Exact checks require Python assertions; run without -O')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--primes', default='5,7,11,13,17,19')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('finite_bridge_receipt.json'))
    args = parser.parse_args()
    primes = [int(x) for x in args.primes.split(',')]
    assert primes and all(p > 3 and all(p % d for d in range(2, int(p**0.5)+1)) for p in primes)
    start = time.monotonic()
    totals, by_prime = verify(primes)
    receipt = {
        'schema': 'trr09-finite-bridge-v1', 'status': 'passed',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'primes': primes, 'coverage': 'Every nonsingular short model over each listed prime field; every triple of rational points; every distinct odd cyclic subgroup.',
        'totals': totals, 'by_prime': by_prime,
        'proof_scope': 'Finite exact controls; universal identities require the accompanying proofs.',
        'elapsed_seconds': round(time.monotonic()-start, 6),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'status': 'passed', 'output': str(args.output), 'totals': totals}))


if __name__ == '__main__':
    main()
