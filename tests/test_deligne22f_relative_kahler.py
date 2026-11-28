"""DEL-22F exact oracle for the relative Kähler presentation over K[a,c].

The quotient is by the *full original* DEL-16 equations and by the
universal section. This checks the explicit derivative coefficient
rows with a_i,c treated as coefficients of P=K[a_i,c].
"""
from __future__ import annotations

import unittest

from tests.test_deligne21g_geometric_fiber import (
    cases, fields, original_jacobian, rank, scheme_equations
)
from tests.test_deligne21h_field_towers import F4_ZERO, embed
from tests.test_deligne22a_relative_critical import derivative_of_section, value_of_section
from tests.test_deligne22b_universal_section import (
    add_poly, evaluate, formal_partial, monomial, mul_poly,
    neg_poly, universal_section,
)


def original_relations(mode, n):
    assert n in (2, 4)
    z = lambda i: monomial(n, {i: 1})
    if mode == "parabola":
        return [add_poly(z(1), neg_poly(mul_poly(z(0), z(0))))]
    if mode in ("node_origin", "node_smooth"):
        return [mul_poly(z(0), z(1))]
    if mode == "double_line":
        return [mul_poly(z(0), z(0))]
    if mode == "radical_line":
        return [z(0)]
    if mode == "redundant":
        sq = mul_poly(z(0), z(0))
        return [sq, mul_poly(sq, z(0))]
    if mode == "product_parabolas":
        return [
            add_poly(z(1), neg_poly(mul_poly(z(0), z(0)))),
            add_poly(z(3), neg_poly(mul_poly(z(2), z(2)))),
        ]
    raise AssertionError(mode)


class UniversalRelativeKahlerOracle(unittest.TestCase):
    def test_relation_gradient_is_literal_augmented_jacobian(self):
        for p, zero, one, alpha in fields():
            for mode, u in cases(zero, one, alpha):
                n = len(u)
                a = tuple((zero, one, alpha)[i % 3] for i in range(n))
                c = -(value_of_section(u, a, zero))
                arguments = tuple(u) + a + (c,)
                rels = [universal_section(n)] + original_relations(mode, n)
                values = [evaluate(rel, arguments) for rel in rels]
                self.assertEqual(values, [zero] * len(rels), (p, mode))
                self.assertEqual(len(rels), len(scheme_equations(mode, *u)) + 1)
                row_values = [
                    [evaluate(formal_partial(rel, j), arguments)
                     for j in range(n)] for rel in rels
                ]
                expected = [
                    list(derivative_of_section(u, a)),
                    *original_jacobian(mode, *u)
                ]
                self.assertEqual(row_values, expected, (p, mode))
                self.assertEqual(rank(row_values), rank(expected), (p, mode))

    def test_parameter_columns_excluded_from_relative_jacobian(self):
        for p, z, one, alpha in fields():
            for mode, u in cases(z, one, alpha):
                n = len(u)
                a = tuple((one, alpha, z)[i % 3] for i in range(n))
                c = z
                assignments = tuple(u) + a + (c,)
                section = universal_section(n)
                for i in range(n):
                    # Absolute derivatives are nonzero in the parameter
                    # directions, but the P-relative presentation has
                    # precisely the n source-coordinate columns.
                    self.assertEqual(
                        evaluate(formal_partial(section, n+i), assignments),
                        u[i], (p, mode, i)
                    )
                self.assertEqual(
                    evaluate(formal_partial(section, 2*n), assignments),
                    one, (p, mode)
                )
                self.assertEqual(
                    [evaluate(formal_partial(section, i), assignments)
                     for i in range(n)],
                    list(derivative_of_section(u, a))
                )

    def test_original_nonreduced_equations_are_not_radicalized(self):
        zero, one = F4_ZERO, F4_ZERO.elt(1)
        point = (zero, zero)
        a = (one, zero)
        arguments = point + a + (zero,)
        thick = original_relations("double_line", 2)
        reduced = original_relations("radical_line", 2)
        redundant = original_relations("redundant", 2)
        self.assertEqual(len(thick), 1)
        self.assertEqual(len(redundant), 2)
        self.assertEqual(
            [evaluate(formal_partial(thick[0], i), arguments) for i in range(2)],
            [zero, zero]
        )
        self.assertEqual(
            [evaluate(formal_partial(reduced[0], i), arguments) for i in range(2)],
            [one, zero]
        )

    def test_f4_to_f16_transports_all_relation_coefficients(self):
        zero, one = F4_ZERO, F4_ZERO.elt(1)
        alpha = zero.elt(0, 1)
        for mode, u in cases(zero, one, alpha):
            n = len(u)
            a = tuple((one, alpha, zero)[i % 3] for i in range(n))
            c = -(value_of_section(u, a, zero))
            args4 = tuple(u) + a + (c,)
            args16 = tuple(map(embed, args4))
            rels = [universal_section(n)] + original_relations(mode, n)
            for rel in rels:
                for j in range(n):
                    d = formal_partial(rel, j)
                    self.assertEqual(
                        embed(evaluate(d, args4)),
                        evaluate(d, args16), (mode, j)
                    )


if __name__ == "__main__":
    unittest.main()
