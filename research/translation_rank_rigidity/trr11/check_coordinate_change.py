#!/usr/bin/env python3
"""Exact generalized-coordinate transport and polynomial-degree controls."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
BASE_PATH = HERE.parent / 'trr10' / 'check_interpolation.py'
SPEC = importlib.util.spec_from_file_location('trr10_interpolation', BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError('Cannot load the exact interpolation implementation')
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
require_equal = BASE.require_equal


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':'), sort_keys=True).encode()).hexdigest()


def invariants(coefficients, p):
    a1, a2, a3, a4, a6 = coefficients
    b2 = (a1*a1 + 4*a2) % p
    b4 = (a1*a3 + 2*a4) % p
    b6 = (a3*a3 + 4*a6) % p
    b8 = (a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4) % p
    c4 = (b2*b2 - 24*b4) % p
    c6 = (-b2**3 + 36*b2*b4 - 216*b6) % p
    delta = (-b2*b2*b8 - 8*b4**3 - 27*b6*b6 + 9*b2*b4*b6) % p
    return b2, b4, b6, b8, c4, c6, delta


def general_coefficients(p, A, B, r, s, t):
    """F(xg,yg)=(xg+r,yg+s*xg+t) maps this model to the short model."""
    return tuple(v % p for v in (
        2*s, 3*r-s*s, 2*t, 3*r*r+A-2*s*t, r**3+A*r+B-t*t))


def normalize(coefficients, p):
    a1, _, a3, _, _ = coefficients
    b2, _, _, _, c4, c6, _ = invariants(coefficients, p)
    return (-c4*pow(48, -1, p) % p, -c6*pow(864, -1, p) % p,
            b2*pow(12, -1, p) % p, a1*pow(2, -1, p) % p,
            a3*pow(2, -1, p) % p)


def forward_point(P, r, s, t, p):
    if P is None:
        return None
    x, y = P
    return (x+r) % p, (y+s*x+t) % p


def inverse_point(P, r, s, t, p):
    if P is None:
        return None
    x, y = P
    return (x-r) % p, (y-s*x+s*r-t) % p


def general_equation(P, coefficients, p):
    if P is None:
        return 0
    x, y = P
    a1, a2, a3, a4, a6 = coefficients
    return (y*y+a1*x*y+a3*y-x**3-a2*x*x-a4*x-a6) % p


def general_add(P, Q, coefficients, p):
    """Direct generalized Weierstrass secant/tangent formulas."""
    if P is None:
        return Q
    if Q is None:
        return P
    a1, a2, a3, a4, _ = coefficients
    x, y = P
    z, w = Q
    if x == z and (y+w+a1*x+a3) % p == 0:
        return None
    if x == z:
        slope = (3*x*x+2*a2*x+a4-a1*y)*pow((2*y+a1*x+a3) % p, -1, p) % p
    else:
        slope = (w-y)*pow((z-x) % p, -1, p) % p
    xx = (slope*slope+a1*slope-a2-x-z) % p
    yy = (-y-a1*xx-a3+slope*(x-xx)) % p
    return xx, yy


def point_orders(add):
    orders = [1]
    for generator in range(1, len(add)):
        current = generator
        order = 1
        while current:
            current = add[current][generator]
            order += 1
            if order > len(add):
                raise AssertionError(('Group order exceeded', generator, order, len(add)))
        orders.append(order)
    return orders


def subgroup_data(points, add, p):
    output = []
    seen = set()
    for generator in range(1, len(points)):
        sequence = [0]
        current = generator
        while current:
            sequence.append(current)
            current = add[current][generator]
        subgroup = frozenset(sequence)
        if len(subgroup) % 2 == 0 or subgroup in seen:
            continue
        seen.add(subgroup)
        nonzero = sorted(subgroup - {0})
        roots = sorted({points[i][0] for i in nonzero})
        denominator = {v: 1 for v in roots}
        for v in roots:
            for w in roots:
                if v != w:
                    denominator[v] = denominator[v]*(v-w) % p
        residues = {i: pow(2*points[i][1]*denominator[points[i][0]] % p, -1, p)
                    for i in nonzero}
        N = len(subgroup)
        output.append({'generator': generator, 'N': N, 'nonzero': nonzero,
                       'roots': roots, 'residues': residues})
    return output


def powers_of_linear(poly, degree, p):
    values = [{(0, 0): 1}]
    for _ in range(degree):
        values.append(BASE.multiply(values[-1], poly, p))
    return values


def affine_pullback(poly, r, s, t, p):
    """Collect coefficients after F in both coordinate pairs."""
    degree = max((max(a+b, c+d) for a, b, c, d in poly), default=0)
    xpoly, ypoly = {(1, 0): 1}, {(0, 1): 1}
    BASE.add_coefficient(xpoly, (0, 0), r, p)
    BASE.add_coefficient(ypoly, (1, 0), s, p)
    BASE.add_coefficient(ypoly, (0, 0), t, p)
    xp, yp = powers_of_linear(xpoly, degree, p), powers_of_linear(ypoly, degree, p)
    pairs = {pair for a, b, c, d in poly for pair in ((a, b), (c, d))}
    basis = {(a, b): BASE.multiply(xp[a], yp[b], p) for a, b in pairs}
    output = {}
    for (a, b, c, d), value in poly.items():
        for left, lc in basis[a, b].items():
            for right, rc in basis[c, d].items():
                BASE.add_coefficient(output, left+right, value*lc*rc, p)
    return output


def transport_decoder(short_decoder, r, s, t, p):
    result = affine_pullback(short_decoder, r, s, t, p)
    BASE.add_coefficient(result, (0, 0, 0, 0), -r, p)
    return result


def evaluate_decoder(poly, P, Q, p):
    x, y = P
    z, w = Q
    return sum(value*pow(x, a, p)*pow(y, b, p)*pow(z, c, p)*pow(w, d, p)
               for (a, b, c, d), value in poly.items()) % p


def curve_multiple(poly, coefficients, degree, p):
    """Same point-table values, with an ordinary block degree above the bound."""
    a1, a2, a3, a4, a6 = coefficients
    result = poly.copy()
    for (a, b), value in [((0, 2), 1), ((1, 1), a1), ((0, 1), a3),
                           ((3, 0), -1), ((2, 0), -a2), ((1, 0), -a4), ((0, 0), -a6)]:
        BASE.add_coefficient(result, (degree+a, b, 0, 0), value, p)
    return result


def shifts_for(p, exhaustive):
    if p in exhaustive:
        return list(product(range(p), repeat=3))
    return sorted({tuple(v % p for v in triple) for triple in
                   [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1), (2, 3, 4)]})


def verify(primes, exhaustive):
    totals = Counter()
    by_prime = {}
    fixtures = []
    witnesses = []
    controls = {}
    seen_fixtures = set()

    def expect_rejected(name, action, context):
        try:
            action()
        except AssertionError as exc:
            controls[name] = {'name': name, 'status': 'rejected', 'fixture': context,
                              'rejection': str(exc)}
            return
        raise AssertionError(('Mutation was accepted', name, context))

    for p in primes:
        counts = Counter()
        shifts = shifts_for(p, exhaustive)
        seen_models = set()
        for A in range(p):
            for B in range(p):
                if (4*A**3+27*B**2) % p == 0:
                    continue
                short_points, short_add, _, short_neg = BASE.BASE.curve_tables(p, A, B)
                short_orders = point_orders(short_add)
                subgroups = subgroup_data(short_points, short_add, p)
                counts['smooth_short_models'] += 1
                for r, s, t in shifts:
                    coefficients = general_coefficients(p, A, B, r, s, t)
                    context = {'p': p, 'short_A': A, 'short_B': B,
                               'r': r, 's': s, 't': t, 'curve_coefficients': coefficients}
                    if coefficients in seen_models:
                        raise AssertionError(('Repeated generalized model', context))
                    seen_models.add(coefficients)
                    counts['generalized_models'] += 1
                    require_equal(normalize(coefficients, p), (A, B, r, s, t),
                                  (context, 'normalization parameters'))
                    _, _, _, _, c4, c6, delta = invariants(coefficients, p)
                    require_equal(delta, -16*(4*A**3+27*B**2) % p, (context, 'discriminant'))
                    require_equal((c4**3-c6*c6) % p, 1728*delta % p,
                                  (context, 'invariant discriminant relation'))
                    if not delta:
                        raise AssertionError(('Singular generated model', context))
                    counts['normalization_invariant_checks'] += 1
                    general_points = [inverse_point(P, r, s, t, p) for P in short_points]
                    lookup = {P: i for i, P in enumerate(general_points)}
                    expected_points = {None} | {(x, y) for x in range(p) for y in range(p)
                                                if general_equation((x, y), coefficients, p) == 0}
                    require_equal(set(general_points), expected_points, (context, 'all rational points'))
                    for i, P in enumerate(general_points):
                        require_equal(forward_point(P, r, s, t, p), short_points[i],
                                      (context, 'point-map inverse', i))
                        require_equal(general_equation(P, coefficients, p), 0,
                                      (context, 'general equation', i))
                        counts['point_coordinate_checks'] += 1
                        if P is not None:
                            x, y = P
                            a1, _, a3, _, _ = coefficients
                            inverse = (x, (-y-a1*x-a3) % p)
                            require_equal(lookup[inverse], short_neg[i], (context, 'negation', i))
                            require_equal((2*y+a1*x+a3) % p, 2*short_points[i][1] % p,
                                          (context, 'vertical derivative factor', i))
                            counts['negation_checks'] += 1
                            counts['vertical_derivative_checks'] += 1
                    general_add_table = [[0]*len(general_points) for _ in general_points]
                    for i, P in enumerate(general_points):
                        for j, Q in enumerate(general_points):
                            R = general_add(P, Q, coefficients, p)
                            require_equal(forward_point(R, r, s, t, p), short_points[short_add[i][j]],
                                          (context, 'group addition', i, j))
                            general_add_table[i][j] = lookup[R]
                            counts['group_addition_checks'] += 1
                            counts['identity_addition_checks'] += int(i == 0 or j == 0)
                            counts['inverse_addition_checks'] += int(i != 0 and j == short_neg[i])
                            counts['nonvertical_tangent_checks'] += int(i == j and short_add[i][j] != 0)
                    require_equal(point_orders(general_add_table), short_orders,
                                  (context, 'exact point orders'))
                    counts['point_order_checks'] += len(general_points)
                    if 'wrong_normalization_x_sign' not in controls and (r, s, t) == (1, 1, 1):
                        def check_wrong_normalization():
                            for P in general_points[1:]:
                                x, y = forward_point(P, -r, s, t, p)
                                require_equal((y*y-x**3-A*x-B) % p, 0,
                                              (context, 'normalized curve equation'))
                        expect_rejected('wrong_normalization_x_sign', check_wrong_normalization, context)
                    for data in subgroups:
                        N, nonzero = data['N'], data['nonzero']
                        degree = (N+2)//3
                        counts['odd_subgroup_instances'] += 1
                        counts['matching_characteristic_subgroup_instances'] += int(N % p == 0)
                        roots = sorted({general_points[i][0] for i in nonzero})
                        require_equal(sorted((v+r) % p for v in roots), data['roots'],
                                      (context, N, 'root translation'))
                        denominator = {v: 1 for v in roots}
                        for v in roots:
                            for w in roots:
                                if v != w:
                                    denominator[v] = denominator[v]*(v-w) % p
                        a1, _, a3, _, _ = coefficients
                        general_residues = {i: pow(((2*general_points[i][1]+a1*general_points[i][0]+a3)*
                                                    denominator[general_points[i][0]]) % p, -1, p)
                                            for i in nonzero}
                        require_equal(general_residues, data['residues'],
                                      (context, N, 'actual residue covariance'))
                        counts['residue_covariance_checks'] += len(nonzero)
                        for d in range(degree+1):
                            monomials = [(a, b) for a in range(d+1) for b in range(d-a+1)]
                            matrix = [[pow(general_points[i][0], a, p)*pow(general_points[i][1], b, p) % p
                                       for a, b in monomials] for i in nonzero]
                            require_equal(BASE.matrix_rank(matrix, p), BASE.expected_rank(N, d),
                                          (context, N, 'ordinary evaluation rank', d))
                            counts['evaluation_rank_checks'] += 1
                        if (p, N) in seen_fixtures or (r, s, t) != (1, 1, 1):
                            continue
                        seen_fixtures.add((p, N))
                        masses = BASE.point_mass_polynomials(nonzero, short_points, data['roots'], p, A, B)
                        for u in (0, 1):
                            short_u = (u+r) % p
                            short_target = {(i, j): short_u if short_add[i][j] == 0
                                            else short_points[short_add[i][j]][0]
                                            for i in nonzero for j in nonzero}
                            general_target = {(i, j): u if general_add_table[i][j] == 0
                                              else general_points[general_add_table[i][j]][0]
                                              for i in nonzero for j in nonzero}
                            short_decoder = BASE.build_decoder(nonzero, masses, short_target, p)
                            decoder = transport_decoder(short_decoder, r, s, t, p)
                            BASE.check_decoder(decoder, nonzero, general_points, general_target,
                                               degree, p, (context, N, u))
                            recovered = affine_pullback(decoder, -r % p, -s % p, (s*r-t) % p, p)
                            BASE.add_coefficient(recovered, (0, 0, 0, 0), r, p)
                            require_equal(recovered, short_decoder, (context, N, u, 'inverse coefficient transport'))
                            counts['explicit_generalized_decoders'] += 1
                            counts['decoder_coefficient_evaluation_checks'] += (N-1)**2
                            counts['inverse_polynomial_coefficient_checks'] += 1
                            encoded = BASE.encoded_polynomial(decoder)
                            generator = data['generator']
                            record = {**context, 'N': N, 'T_general': general_points[generator],
                                      'T_short': short_points[generator], 'u_general': u,
                                      'u_short': short_u, 'degree_bound': degree,
                                      'decoder_terms': len(decoder), 'decoder_sha256': digest(encoded),
                                      'short_decoder_sha256': digest(BASE.encoded_polynomial(short_decoder)),
                                      'left_degree': max((a+b for a, b, c, d in decoder), default=0),
                                      'right_degree': max((c+d for a, b, c, d in decoder), default=0),
                                      'verified_target_entries': (N-1)**2}
                            fixtures.append(record)
                            witnesses.append({**record, 'variables': ['X1', 'Y1', 'X2', 'Y2'],
                                              'coefficients': encoded})
                            if 'unshifted_assigned_identity_value' not in controls:
                                wrong_target = {(i, j): u if short_add[i][j] == 0
                                                else short_points[short_add[i][j]][0]
                                                for i in nonzero for j in nonzero}
                                bad = transport_decoder(BASE.build_decoder(nonzero, masses, wrong_target, p),
                                                        r, s, t, p)
                                for i in nonzero:
                                    for j in nonzero:
                                        if general_add_table[i][j] != 0:
                                            require_equal(evaluate_decoder(bad, general_points[i], general_points[j], p),
                                                          general_target[i, j], 'wrong-u nonidentity output still agrees')
                                expect_rejected('unshifted_assigned_identity_value',
                                    lambda: BASE.check_decoder(bad, nonzero, general_points, general_target,
                                                               degree, p, 'wrong assigned-value shift'), record)
                            if 'curve_multiple_exceeds_block_degree' not in controls:
                                bad = curve_multiple(decoder, coefficients, degree, p)
                                BASE.check_decoder(bad, nonzero, general_points, general_target, degree+3, p,
                                                   'curve multiple preserves all table entries')
                                expect_rejected('curve_multiple_exceeds_block_degree',
                                    lambda: BASE.check_decoder(bad, nonzero, general_points, general_target,
                                                               degree, p, 'higher-degree identical table'), record)
        expected_models = (p*p-p)*len(shifts)
        require_equal(len(seen_models), expected_models, (p, 'model count'))
        if p in exhaustive:
            require_equal(len(seen_models), p**5-p**4, (p, 'all smooth generalized models'))
            all_smooth = {coefficients for coefficients in product(range(p), repeat=5)
                          if invariants(coefficients, p)[-1] != 0}
            require_equal(seen_models, all_smooth, (p, 'independent full coefficient-grid coverage'))
            counts['raw_coefficient_tuples_checked'] = p**5
            counts['raw_smooth_models_checked'] = len(all_smooth)
        by_prime[str(p)] = {'coverage': 'all smooth generalized models' if p in exhaustive else
                           'all smooth short models under the listed affine coordinate changes',
                           'affine_triples_per_short_model': len(shifts),
                           'affine_triples': 'all of F_p^3' if p in exhaustive else shifts,
                           'counts': dict(counts)}
        totals.update(counts)
        print(f'Passed p={p}: {counts["generalized_models"]} generalized models, '
              f'{counts["group_addition_checks"]} additions, '
              f'{counts["evaluation_rank_checks"]} ranks, '
              f'{counts["explicit_generalized_decoders"]} coefficient decoders', flush=True)
    require_equal(set(controls), {'wrong_normalization_x_sign', 'unshifted_assigned_identity_value',
                                  'curve_multiple_exceeds_block_degree'}, 'mutation coverage')
    return dict(totals), by_prime, fixtures, witnesses, list(controls.values())


def main():
    if not __debug__:
        raise RuntimeError('Exact checks require Python assertions; run without -O')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--primes', default='5,7,11,13,17,19')
    parser.add_argument('--exhaustive-primes', default='5,7')
    parser.add_argument('--output', type=Path, default=HERE / 'coordinate_change_receipt.json')
    parser.add_argument('--witness-output', type=Path)
    args = parser.parse_args()
    primes = [int(value) for value in args.primes.split(',')]
    exhaustive = {int(value) for value in args.exhaustive_primes.split(',') if value}
    if not primes or any(p <= 3 or any(p % d == 0 for d in range(2, int(p**0.5)+1)) for p in primes):
        raise ValueError('Every requested characteristic must be prime and greater than three')
    if len(set(primes)) != len(primes) or not exhaustive.issubset(primes):
        raise ValueError('Repeated fields or an exhaustive field outside the field list')
    start = time.monotonic()
    totals, by_prime, fixtures, witnesses, controls = verify(primes, exhaustive)
    coverage = []
    if exhaustive:
        fields = ', '.join(f'F{p}' for p in sorted(exhaustive))
        coverage.append(f'Every smooth generalized model over {fields}, checked against the independent five-coefficient grid.')
    selected = [p for p in primes if p not in exhaustive]
    if selected:
        fields = ', '.join(f'F{p}' for p in selected)
        coverage.append(f'Six listed affine changes of every smooth short model over {fields}.')
    receipt = {'schema': 'trr11-coordinate-change-controls-v1', 'status': 'passed',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'interpolation_source_sha256': hashlib.sha256(BASE_PATH.read_bytes()).hexdigest(),
        'curve_table_source_sha256': hashlib.sha256(BASE.BASE_PATH.read_bytes()).hexdigest(),
        'primes': primes, 'exhaustive_generalized_fields': sorted(exhaustive),
        'coordinate_orientation': 'F(x_general,y_general)=(x_general+r,y_general+s*x_general+t) in short coordinates; F(O)=O.',
        'inverse_orientation': 'F_inverse(x_short,y_short)=(x_short-r,y_short-s*x_short+s*r-t).',
        'normalization_parameters': 'r=b2/12, s=a1/2, t=a3/2, A=-c4/48, B=-c6/864.',
        'decoder_transport': 'D_general=D_short(F(first pair),F(second pair))-r with u_short=u_general+r.',
        'coverage': ' '.join(coverage),
        'curve_coefficient_order': ['a1', 'a2', 'a3', 'a4', 'a6'],
        'decoder_fixture_rule': 'First subgroup for each (p,N), ordered by short A,B and point coordinates; affine triple (1,1,1); u_general=0 and 1.',
        'totals': totals, 'by_prime': by_prime, 'decoder_fixtures': fixtures,
        'mutation_controls': controls, 'witness_bundle_sha256': digest(witnesses),
        'proof_scope': 'Finite exact controls of generalized-coordinate transport; universal statements use the accompanying Lean proofs.',
        'elapsed_seconds': round(time.monotonic()-start, 6)}
    if args.witness_output is not None:
        args.witness_output.parent.mkdir(parents=True, exist_ok=True)
        args.witness_output.write_text(json.dumps({'schema': 'trr11-generalized-decoders-v1',
            'field_convention': 'Coefficients and coordinates are canonical residues modulo p.',
            'curve_coefficient_order': ['a1', 'a2', 'a3', 'a4', 'a6'],
            'decoder_fixtures': witnesses}, separators=(',', ':'))+'\n')
        receipt['witness_output_sha256'] = hashlib.sha256(args.witness_output.read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'status': 'passed', 'output': str(args.output), 'totals': totals,
                      'elapsed_seconds': receipt['elapsed_seconds']}), flush=True)


if __name__ == '__main__':
    main()
