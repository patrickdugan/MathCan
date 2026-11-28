"""DEL-22B independent arithmetic oracle for K[a_i,c][z] specialization.

Sparse integer polynomials represent the universal fixed-last-coefficient
section with independent source and parameter variables. The evaluator
checks section values, z-partial derivatives and augmented determinant
minors over GF(4), GF(9) and the GF(4)->GF(16) embedding.
"""
from __future__ import annotations

from itertools import combinations, product
import unittest

from tests.test_deligne21g_geometric_fiber import (
    cases, fields, original_jacobian, scheme_equations
)
from tests.test_deligne21h_field_towers import F4_ZERO, embed
from tests.test_deligne22a_relative_critical import (
    derivative_of_section, determinant, value_of_section
)


def monomial(n, powers, coefficient=1):
    exp = [0] * (2 * n + 1)
    for i, v in powers.items():
        exp[i] = v
    return {tuple(exp): coefficient}


def add_poly(*polys):
    out = {}
    for p in polys:
        for exp, coeff in p.items():
            out[exp] = out.get(exp, 0) + coeff
    return {k: v for k, v in out.items() if v}


def neg_poly(poly):
    return {exp: -v for exp, v in poly.items()}


def mul_poly(a, b):
    out = {}
    for x, ca in a.items():
        for y, cb in b.items():
            z = tuple(u + v for u, v in zip(x, y))
            out[z] = out.get(z, 0) + ca * cb
    return {k: v for k, v in out.items() if v}


def universal_section(n):
    assert n in (2, 4)
    b = monomial(n, {0: 1, 1 if n == 2 else 2: 1})
    parameter_terms = [monomial(n, {i: 1, n + i: 1}) for i in range(n)]
    return add_poly(b, *parameter_terms, monomial(n, {2 * n: 1}))


def formal_partial(poly, variable):
    out = {}
    for exp, coeff in poly.items():
        if exp[variable]:
            new = list(exp)
            new[variable] -= 1
            key = tuple(new)
            out[key] = out.get(key, 0) + coeff * exp[variable]
    return {k: v for k, v in out.items() if v}


def evaluate(poly, assignments):
    zero = assignments[0].elt(0)
    total = zero
    for exp, coeff in poly.items():
        term = assignments[0].elt(coeff)
        for v, e in zip(assignments, exp):
            if e:
                term *= v ** e
        total += term
    return total


def universal_original_rows(mode, n):
    z = {}
    one = monomial(n, {})
    x = monomial(n, {0: 1})
    y = monomial(n, {1: 1})
    if mode == "parabola":
        return [[neg_poly(add_poly(x, x)), one]]
    if mode in ("node_origin", "node_smooth"):
        return [[y, x]]
    if mode == "double_line":
        return [[add_poly(x, x), z]]
    if mode == "radical_line":
        return [[one, z]]
    if mode == "redundant":
        return [[add_poly(x, x), z],
                [add_poly(*([mul_poly(x, x)] * 3)), z]]
    if mode == "product_parabolas":
        x2 = monomial(n, {2: 1})
        return [[neg_poly(add_poly(x, x)), one, z, z],
                [z, z, neg_poly(add_poly(x2, x2)), one]]
    raise AssertionError(mode)


def determinant_poly(rows):
    n = len(rows)
    assert n >= 1
    if n == 1:
        return rows[0][0]
    out = {}
    for j, p in enumerate(rows[0]):
        sub = [row[:j] + row[j + 1:] for row in rows[1:]]
        term = mul_poly(p, determinant_poly(sub))
        out = add_poly(out, neg_poly(term) if j % 2 else term)
    return out


class UniversalRelativeCriticalOracle(unittest.TestCase):
    def test_specialization_of_section_gradient_and_minors(self):
        for p, zero, one, alpha in fields():
            for mode, u in cases(zero, one, alpha):
                self.assertTrue(all(v == zero for v in scheme_equations(mode, *u)))
                n = len(u)
                s = universal_section(n)
                a = tuple((one, alpha, zero)[i % 3] for i in range(n))
                c = alpha + one
                values = tuple(u) + a + (c,)
                self.assertEqual(evaluate(s, values), value_of_section(u, a, c),
                                 (p, mode))
                g = [formal_partial(s, i) for i in range(n)]
                numeric_g = derivative_of_section(u, a)
                self.assertEqual(tuple(evaluate(x, values) for x in g),
                                 numeric_g, (p, mode))
                polynomial = universal_original_rows(mode, n) + [g]
                numeric = original_jacobian(mode, *u) + [list(numeric_g)]
                for rowp, rowv in zip(polynomial, numeric):
                    for entry, value in zip(rowp, rowv):
                        self.assertEqual(evaluate(entry, values), value)
                max_size = min(len(numeric), n)
                for size in range(1, max_size + 1):
                    for rr in combinations(range(len(numeric)), size):
                        for cc in combinations(range(n), size):
                            minor = [[polynomial[i][j] for j in cc] for i in rr]
                            minor_values = [[numeric[i][j] for j in cc] for i in rr]
                            self.assertEqual(evaluate(determinant_poly(minor), values),
                                             determinant(minor_values), (p, mode, rr, cc))

    def test_gf4_to_gf16_universal_specialization_commutes(self):
        zero = F4_ZERO
        one = zero.elt(1)
        alpha = zero.elt(0, 1)
        for mode, u in cases(zero, one, alpha):
            n = len(u)
            a = tuple((one, alpha, zero)[i % 3] for i in range(n))
            c = alpha
            values = tuple(u) + a + (c,)
            values16 = tuple(map(embed, values))
            s = universal_section(n)
            polynomials = [s] + [formal_partial(s, i) for i in range(n)]
            for pol in polynomials:
                self.assertEqual(embed(evaluate(pol, values)),
                                 evaluate(pol, values16), mode)


if __name__ == "__main__":
    unittest.main()
