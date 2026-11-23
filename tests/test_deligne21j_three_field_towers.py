"""DEL-21J exact arithmetic checks for compatible three-stage field maps.

Lean proves equality of the complete original-scheme cotangent and tangent
base-change equivalences. These independent finite-field checks exercise the
pure-tensor coordinate and relation formulas with the original Jacobian rows.
"""
from __future__ import annotations

from itertools import product
import unittest

from tests.test_deligne21h_field_towers import (
    F4, F4_ZERO, F16, GF16, embed, dot,
    row_span as gf16_row_span,
)
from tests.test_deligne21g_geometric_fiber import (
    Fp2, cases, original_jacobian, rank, scheme_equations,
)


class Deligne21JThreeFieldTowerOracle(unittest.TestCase):
    def test_gf2_gf4_gf16_two_step_tensor_coordinates(self):
        z4, one4 = F4_ZERO, F4_ZERO.elt(1)
        z16 = GF16(0)
        # The GF(2) -> GF(4) inclusion is represented by F4 constants.
        # GF(4) -> GF(16) sends alpha to theta^5 (DEL-21H's exact map).
        for mode, u in cases(z4, one4, one4):
            self.assertTrue(all(x in (z4, one4) for x in u), mode)
            self.assertTrue(all(x == z4 for x in scheme_equations(mode, *u)))
            rows4 = original_jacobian(mode, *u)
            rows16 = original_jacobian(mode, *tuple(map(embed, u)))
            self.assertEqual(rows16, [[embed(a) for a in row] for row in rows4])
            for bits in product((0, 1), repeat=len(rows4[0])):
                v4 = tuple(z4.elt(a) for a in bits)
                for m in F4:
                    for n in (z16, GF16(1), GF16(5), GF16(15)):
                        direct = tuple((embed(m) * n) * GF16(a) for a in bits)
                        two_step = tuple(n * embed(m * a) for a in v4)
                        self.assertEqual(direct, two_step, (mode, bits, m, n))
                        if all(dot(row, v4) == z4 for row in rows4):
                            self.assertTrue(all(
                                dot(row, direct) == z16 for row in rows16
                            ), (mode, bits, m, n))

    def test_relation_ideals_transport_in_characteristic_two(self):
        z4, one4 = F4_ZERO, F4_ZERO.elt(1)
        for mode, u in cases(z4, one4, one4):
            rows4 = original_jacobian(mode, *u)
            rows16 = original_jacobian(mode, *tuple(map(embed, u)))
            relations16 = gf16_row_span(F16, rows16)
            for lam in product((z4, one4), repeat=len(rows4)):
                relation = tuple(
                    sum((lam[t] * rows4[t][i] for t in range(len(rows4))), z4)
                    for i in range(len(rows4[0]))
                )
                self.assertIn(tuple(map(embed, relation)), relations16, mode)
            if mode == "double_line":
                self.assertEqual(rank(rows4), 0)
                self.assertEqual(rank(rows16), 0)
            elif mode == "radical_line":
                self.assertEqual(rank(rows4), 1)
                self.assertEqual(rank(rows16), 1)

    def test_gf3_gf9_frobenius_three_stage_naturality(self):
        # The maps are GF(3) -> GF(9) -> GF(9), where the second is
        # the nontrivial GF(3)-algebra automorphism x -> x^3.
        z9 = Fp2(0, 0, 3, 0, 1)
        one9 = z9.elt(1)
        a9 = z9.elt(0, 1)
        scalars9 = [z9.elt(a, b) for a, b in product(range(3), repeat=2)]

        def frob(x: Fp2) -> Fp2:
            return x ** 3

        self.assertEqual(frob(a9), -a9)
        for x, y in product(scalars9, repeat=2):
            self.assertEqual(frob(x + y), frob(x) + frob(y))
            self.assertEqual(frob(x * y), frob(x) * frob(y))
        for mode, u in cases(z9, one9, one9):
            self.assertTrue(all(x == z9 for x in scheme_equations(mode, *u)))
            rows = original_jacobian(mode, *u)
            moved_u = tuple(map(frob, u))
            moved_rows = original_jacobian(mode, *moved_u)
            self.assertEqual(moved_rows, [[frob(x) for x in row] for row in rows])
            for digits in product(range(3), repeat=len(rows[0])):
                v = tuple(z9.elt(x) for x in digits)
                for m in scalars9:
                    for n in (z9, one9, a9, a9 + one9):
                        direct = tuple((frob(m) * n) * frob(x) for x in v)
                        two_step = tuple(n * frob(m * x) for x in v)
                        self.assertEqual(direct, two_step, (mode, digits, m, n))
                        if all(dot(row, v) == z9 for row in rows):
                            self.assertTrue(all(
                                dot(row, direct) == z9 for row in moved_rows
                            ), (mode, digits, m, n))


if __name__ == "__main__":
    unittest.main()
