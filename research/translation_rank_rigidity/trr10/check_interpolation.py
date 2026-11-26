#!/usr/bin/env python3
"""Exact finite controls for residue annihilation and ordinary-degree interpolation."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
BASE_PATH = HERE.parent / 'trr09' / 'check_finite_bridge.py'
SPEC = importlib.util.spec_from_file_location('trr09_curve_tables', BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError('Cannot load the exact curve-table implementation')
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)


def require_equal(actual, expected, context):
    if actual != expected:
        raise AssertionError((context, actual, expected))


def add_coefficient(poly, exponent, coefficient, p):
    value = (poly.get(exponent, 0) + coefficient) % p
    if value:
        poly[exponent] = value
    else:
        poly.pop(exponent, None)


def add_scaled(target, source, scalar, p):
    for exponent, coefficient in source.items():
        add_coefficient(target, exponent, scalar * coefficient, p)


def multiply(left, right, p):
    result = {}
    for (a, b), c in left.items():
        for (i, j), d in right.items():
            add_coefficient(result, (a+i, b+j), c*d, p)
    return result


def lift_powers(length, p, A, B):
    """Actual ordinary polynomials representing x^j on the short cubic."""
    cubic_replacement = {(0, 2): 1}
    add_coefficient(cubic_replacement, (1, 0), -A, p)
    add_coefficient(cubic_replacement, (0, 0), -B, p)
    powers = [{(0, 0): 1}]
    for _ in range(length // 3):
        powers.append(multiply(powers[-1], cubic_replacement, p))
    return [{(a+j % 3, b): c for (a, b), c in powers[j // 3].items()}
            for j in range(length)]


def lagrange_coefficients(roots, a, p):
    coefficients = [1]
    denominator = 1
    for v in roots:
        if v == a:
            continue
        result = [0] * (len(coefficients) + 1)
        for j, c in enumerate(coefficients):
            result[j] = (result[j] - v*c) % p
            result[j+1] = (result[j+1] + c) % p
        coefficients = result
        denominator = denominator * (a-v) % p
    scale = pow(denominator, -1, p)
    return [c*scale % p for c in coefficients]


def point_mass_polynomials(nonzero, points, roots, p, A, B):
    lifts = lift_powers(len(roots), p, A, B)
    basis = {}
    for a in roots:
        result = {}
        for j, coefficient in enumerate(lagrange_coefficients(roots, a, p)):
            add_scaled(result, lifts[j], coefficient, p)
        basis[a] = result
    output = {}
    half = pow(2, -1, p)
    for i in nonzero:
        a, b = points[i]
        poly = {}
        add_scaled(poly, basis[a], half, p)
        for (j, k), coefficient in basis[a].items():
            add_coefficient(poly, (j, k+1), coefficient*pow(2*b, -1, p), p)
        output[i] = poly
    return output


def ordinary_degree(poly):
    return max((a+b for a, b in poly), default=0)


def check_ordinary_degree(poly, degree, context):
    actual = ordinary_degree(poly)
    if actual > degree:
        raise AssertionError((context, 'ordinary total degree', actual, degree))


def evaluate(poly, point, p):
    x, y = point
    return sum(c*pow(x, a, p)*pow(y, b, p) for (a, b), c in poly.items()) % p


def matrix_rank(rows, p):
    matrix = [row[:] for row in rows]
    rank = 0
    columns = len(matrix[0]) if matrix else 0
    for column in range(columns):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][column] % p), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inv = pow(matrix[rank][column] % p, -1, p)
        matrix[rank] = [(v*inv) % p for v in matrix[rank]]
        for i in range(rank+1, len(matrix)):
            factor = matrix[i][column] % p
            if factor:
                matrix[i] = [(v-factor*w) % p for v, w in zip(matrix[i], matrix[rank])]
        rank += 1
        if rank == len(matrix):
            break
    return rank


def expected_rank(N, degree):
    if degree == 0:
        return 1
    return min(3*degree, N-1) - int(3*degree == N-1)


def build_decoder(nonzero, point_masses, target, p):
    """Collect the actual four-variable coefficients of the tensor interpolant."""
    decoder = {}
    for i in nonzero:
        right = {}
        for j in nonzero:
            add_scaled(right, point_masses[j], target[i, j], p)
        for left_power, left_coefficient in point_masses[i].items():
            for right_power, right_coefficient in right.items():
                add_coefficient(decoder, left_power + right_power,
                                left_coefficient * right_coefficient, p)
    return decoder


def check_decoder(decoder, nonzero, points, target, degree, p, context):
    for a, b, c, d in decoder:
        if a+b > degree or c+d > degree:
            raise AssertionError((context, 'block degree', (a, b, c, d), degree))
    # Evaluate the collected coefficients by specializing the first coordinate
    # pair. This uses neither the point-mass identity nor the target in evaluation.
    for i in nonzero:
        x, y = points[i]
        specialized = {}
        for (a, b, c, d), coefficient in decoder.items():
            add_coefficient(specialized, (c, d), coefficient*pow(x, a, p)*pow(y, b, p), p)
        for j in nonzero:
            require_equal(evaluate(specialized, points[j], p), target[i, j],
                          (context, 'decoder evaluation', i, j))


def encoded_polynomial(poly):
    return [[*exponent, coefficient] for exponent, coefficient in sorted(poly.items())]


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':'), sort_keys=True).encode()).hexdigest()


def verify(primes):
    totals = Counter()
    by_prime = {}
    fixtures = []
    witnesses = []
    seen_fixtures = set()
    controls = {}

    def expect_rejected(name, action, fixture):
        try:
            action()
        except AssertionError:
            controls[name] = {'name': name, 'status': 'rejected', 'fixture': fixture}
            return
        raise AssertionError(('Mutation was accepted', name, fixture))

    for p in primes:
        counts = Counter()
        for A in range(p):
            for B in range(p):
                if (4*A**3+27*B**2) % p == 0:
                    continue
                points, add, _, neg = BASE.curve_tables(p, A, B)
                counts['smooth_models'] += 1
                seen_subgroups = set()
                for generator in range(1, len(points)):
                    sequence = [0]
                    current = generator
                    while current:
                        sequence.append(current)
                        current = add[current][generator]
                    subgroup = frozenset(sequence)
                    if subgroup in seen_subgroups or len(subgroup) % 2 == 0:
                        continue
                    seen_subgroups.add(subgroup)
                    N = len(subgroup)
                    nonzero = sorted(subgroup - {0})
                    roots = sorted({points[i][0] for i in nonzero})
                    m = len(roots)
                    D = (N+2) // 3
                    context = (p, A, B, N, points[generator])
                    counts['odd_cyclic_subgroups'] += 1
                    counts['matching_characteristic_subgroups'] += int(N % p == 0)
                    counts[f'order_residue_mod_3_{N % 3}'] += 1
                    require_equal(2*m+1, N, (context, 'root cardinality'))
                    counts['root_cardinality_checks'] += 1
                    denominator = {v: 1 for v in roots}
                    for v in roots:
                        for w in roots:
                            if v != w:
                                denominator[v] = denominator[v]*(v-w) % p
                    residues = {i: pow(2*points[i][1]*denominator[points[i][0]] % p, -1, p)
                                for i in nonzero}
                    low_degree = (N-1) // 3
                    for a in range(low_degree+1):
                        for b in range(low_degree-a+1):
                            value = sum(residues[i]*pow(points[i][0], a, p)*
                                        pow(points[i][1], b, p) for i in nonzero) % p
                            require_equal(value, 0, (context, 'residue monomial', a, b))
                            counts['annihilated_monomial_checks'] += 1
                    rank_profile = []
                    for degree in range(D+1):
                        monomials = [(a, b) for a in range(degree+1)
                                     for b in range(degree-a+1)]
                        rows = [[pow(points[i][0], a, p)*pow(points[i][1], b, p) % p
                                 for a, b in monomials] for i in nonzero]
                        rank = matrix_rank(rows, p)
                        require_equal(rank, expected_rank(N, degree), (context, 'evaluation rank', degree))
                        rank_profile.append(rank)
                        counts['evaluation_rank_checks'] += 1
                    masses = point_mass_polynomials(nonzero, points, roots, p, A, B)
                    for i in nonzero:
                        check_ordinary_degree(masses[i], D, (context, 'point mass', i))
                        counts['point_mass_degree_checks'] += 1
                        for j in nonzero:
                            require_equal(evaluate(masses[i], points[j], p), int(i == j),
                                          (context, 'point mass evaluation', i, j))
                            counts['point_mass_evaluation_checks'] += 1
                    leading_value = lambda weights: sum(weights[i]*points[i][1]*
                        pow(points[i][0], m-1, p) for i in nonzero) % p
                    require_equal(leading_value(residues), 1, (context, 'leading odd coefficient'))
                    counts['leading_coefficient_checks'] += 1
                    fixture_key = {'p': p, 'A': A, 'B': B, 'N': N, 'T': points[generator]}
                    if 'missing_residue_factor_two' not in controls:
                        bad = {i: 2*v % p for i, v in residues.items()}
                        expect_rejected('missing_residue_factor_two',
                            lambda: require_equal(leading_value(bad), 1, 'leading odd coefficient'), fixture_key)
                    if 'wrong_residue_negation_sign' not in controls:
                        bad = residues.copy()
                        for v in roots:
                            representative = next(i for i in nonzero if points[i][0] == v)
                            bad[neg[representative]] = bad[representative]
                        expect_rejected('wrong_residue_negation_sign',
                            lambda: require_equal(leading_value(bad), 1, 'leading odd coefficient'), fixture_key)
                    if 'uncompressed_ordinary_degree' not in controls and m > D:
                        i = nonzero[0]
                        coefficients = lagrange_coefficients(roots, points[i][0], p)
                        naive = {}
                        for j, coefficient in enumerate(coefficients):
                            add_coefficient(naive, (j, 0), coefficient*pow(2, -1, p), p)
                            add_coefficient(naive, (j, 1), coefficient*pow(2*points[i][1], -1, p), p)
                        for j in nonzero:
                            require_equal(evaluate(naive, points[j], p), int(i == j), 'naive values')
                        expect_rejected('uncompressed_ordinary_degree',
                            lambda: check_ordinary_degree(naive, D, 'naive lift'), fixture_key)
                    if (p, N) not in seen_fixtures:
                        seen_fixtures.add((p, N))
                        for u in (0, 1):
                            target = {(i, j): u if add[i][j] == 0 else points[add[i][j]][0]
                                      for i in nonzero for j in nonzero}
                            decoder = build_decoder(nonzero, masses, target, p)
                            check_decoder(decoder, nonzero, points, target, D, p, (context, u))
                            encoded = encoded_polynomial(decoder)
                            record = {**fixture_key, 'u': u, 'degree_bound': D,
                                'evaluation_ranks_degrees_0_through_bound': rank_profile,
                                'decoder_terms': len(decoder), 'decoder_sha256': digest(encoded),
                                'left_degree': max((a+b for a, b, c, d in decoder), default=0),
                                'right_degree': max((c+d for a, b, c, d in decoder), default=0),
                                'verified_target_entries': (N-1)**2}
                            fixtures.append(record)
                            witnesses.append({**record, 'variables': ['X1', 'Y1', 'X2', 'Y2'],
                                              'coefficients': encoded})
                            counts['explicit_decoder_fixtures'] += 1
                            counts['decoder_coefficient_evaluation_checks'] += (N-1)**2
        by_prime[str(p)] = dict(counts)
        totals.update(counts)
        print(f'Passed p={p}: {counts["smooth_models"]} models, '
              f'{counts["odd_cyclic_subgroups"]} odd subgroups, '
              f'{counts["evaluation_rank_checks"]} ranks, '
              f'{counts["explicit_decoder_fixtures"]} collected decoders', flush=True)
    require_equal(set(controls), {'missing_residue_factor_two', 'wrong_residue_negation_sign',
                                  'uncompressed_ordinary_degree'}, 'mutation coverage')
    return dict(totals), by_prime, fixtures, witnesses, list(controls.values())


def main():
    if not __debug__:
        raise RuntimeError('Exact checks require Python assertions; run without -O')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--primes', default='5,7,11,13,17,19')
    parser.add_argument('--output', type=Path, default=HERE / 'interpolation_receipt.json')
    parser.add_argument('--witness-output', type=Path)
    args = parser.parse_args()
    primes = [int(value) for value in args.primes.split(',')]
    if not primes or any(p <= 3 or any(p % d == 0 for d in range(2, int(p**0.5)+1)) for p in primes):
        raise ValueError('Every requested field characteristic must be prime and greater than three')
    if len(set(primes)) != len(primes):
        raise ValueError('Repeated fields would duplicate the coverage counts')
    start = time.monotonic()
    totals, by_prime, fixtures, witnesses, controls = verify(primes)
    receipt = {'schema': 'trr10-interpolation-controls-v1', 'status': 'passed',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'curve_table_source_sha256': hashlib.sha256(BASE_PATH.read_bytes()).hexdigest(),
        'primes': primes,
        'coverage': 'Every nonsingular short model and every distinct nontrivial odd cyclic subgroup over each listed prime field.',
        'rank_rule': 'rank(0)=1; rank(d)=min(3*d,N-1)-int(3*d==N-1) for 1<=d<=ceil(N/3).',
        'decoder_fixture_rule': 'First subgroup encountered for each (p,N), ordered by A,B and point coordinates; both u=0 and u=1.',
        'totals': totals, 'by_prime': by_prime, 'decoder_fixtures': fixtures,
        'mutation_controls': controls, 'witness_bundle_sha256': digest(witnesses),
        'proof_scope': 'Finite exact controls for the stated interpolation model; universal conclusions use the accompanying Lean proofs.',
        'elapsed_seconds': round(time.monotonic()-start, 6)}
    if args.witness_output is not None:
        args.witness_output.parent.mkdir(parents=True, exist_ok=True)
        args.witness_output.write_text(json.dumps({'schema': 'trr10-explicit-decoders-v1',
            'field_convention': 'Coefficients and coordinates are canonical residues modulo p.',
            'decoder_fixtures': witnesses}, separators=(',', ':'))+'\n')
        receipt['witness_output_sha256'] = hashlib.sha256(args.witness_output.read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'status': 'passed', 'output': str(args.output), 'totals': totals,
                      'elapsed_seconds': receipt['elapsed_seconds']}), flush=True)


if __name__ == '__main__':
    main()
