"""DEL-21F: independent finite-field oracles for the actual Kähler point fiber.

Lean proves the genuine Kähler-module equivalence.  These arithmetic
controls check its explicitly identified Jacobian coordinates against the
original polynomial equations and flag nonreduced-to-radical mutation.
"""
from __future__ import annotations

import itertools
import unittest

from tests.test_deligne21d_conormal_fiber import (
    PRIMES,
    dot,
    frozen,
    gradients_for_mode,
    is_tangent,
    rank_mod,
    row_span,
)


def defining_values(mode: str, point: list[int], p: int) -> list[int]:
    """Evaluate the original lifted equations, with their multiplicities."""
    x, y = point[:2]
    if mode in ("parabola", "char_two"):
        return [(y - x * x) % p]
    if mode in ("node_origin", "node_smooth"):
        return [x * y % p]
    if mode == "double_line":
        return [x * x % p]
    if mode == "radical_line":
        return [x % p]
    if mode == "redundant":
        return [x * x % p, x * x * x % p]
    if mode == "product_parabolas":
        a, b = point[2:]
        return [(y - x * x) % p, (b - a * a) % p]
    raise AssertionError(f"Unknown mode {mode}")


def quotient_class(v: tuple[int, ...], rows: list[list[int]], p: int):
    """Canonical finite representative modulo the span of the real rows."""
    rel = row_span(rows, p)
    return min(
        tuple((v[i] + w[i]) % p for i in range(len(v)))
        for w in rel
    )


class ActualKahlerFiberOracle(unittest.TestCase):
    def test_all_frozen_points_satisfy_original_equations(self):
        cases = frozen()
        self.assertEqual(len(cases), 160)
        for c in cases:
            p = int(c["field"][1:])
            self.assertEqual(
                defining_values(c["mode"], c["point"], p),
                [0] * len(c["jacobian"]),
                c["id"],
            )

    def test_base_changed_relation_rows_are_true_gradients(self):
        for c in frozen():
            p = int(c["field"][1:])
            rows = gradients_for_mode(c["mode"], c["point"], p)
            self.assertEqual(rows, c["jacobian"], c["id"])
            self.assertEqual(rank_mod(rows, p), c["rank"], c["id"])

    def test_cokernel_and_dual_dimensions(self):
        for c in frozen():
            p = int(c["field"][1:])
            n = c["coordinates"]
            rel_rank = rank_mod(c["jacobian"], p)
            self.assertEqual(c["presented_cotangent_dim"], n - rel_rank)
            self.assertEqual(c["expected_tangent_count"], p ** (n - rel_rank))
            if p <= 5:
                tangents = sum(
                    is_tangent(c["jacobian"], v, p)
                    for v in itertools.product(range(p), repeat=n)
                )
                self.assertEqual(tangents, p ** (n - rel_rank))

    def test_quotient_pairing_is_well_defined(self):
        for c in frozen():
            p = int(c["field"][1:])
            if p > 5:
                continue
            n = c["coordinates"]
            rows = c["jacobian"]
            for v in itertools.product(range(p), repeat=n):
                if not is_tangent(rows, v, p):
                    continue
                for x in itertools.product(range(p), repeat=n):
                    canonical = quotient_class(x, rows, p)
                    self.assertEqual(dot(p, v, x), dot(p, v, canonical))

    def test_nonreduced_ideal_is_not_its_radical(self):
        for p in PRIMES:
            thick, reduced = [[0, 0]], [[1, 0]]
            self.assertEqual(rank_mod(thick, p), 0)
            self.assertEqual(rank_mod(reduced, p), 1)
            self.assertNotEqual(row_span(thick, p), row_span(reduced, p))
            self.assertTrue(is_tangent(thick, (1, 0), p))
            self.assertFalse(is_tangent(reduced, (1, 0), p))

    def test_node_origin_and_smooth_point(self):
        for p in PRIMES:
            self.assertEqual(gradients_for_mode("node_origin", [0, 0], p),
                             [[0, 0]])
            self.assertEqual(gradients_for_mode("node_smooth", [1, 0], p),
                             [[0, 1]])
            self.assertEqual(rank_mod([[0, 0]], p), 0)
            self.assertEqual(rank_mod([[0, 1]], p), 1)

    def test_redundant_generators_same_full_ideal(self):
        for p in PRIMES:
            self.assertEqual(
                row_span(gradients_for_mode("redundant", [0, 0], p), p),
                row_span(gradients_for_mode("double_line", [0, 0], p), p),
            )

    def test_characteristic_two_and_product_factors(self):
        self.assertEqual(gradients_for_mode("char_two", [1, 1], 2), [[0, 1]])
        for c in frozen():
            if c["mode"] != "product_parabolas":
                continue
            p = int(c["field"][1:])
            self.assertEqual(rank_mod(c["jacobian"], p), 2)
            self.assertEqual(c["jacobian"][0][2:], [0, 0])
            self.assertEqual(c["jacobian"][1][:2], [0, 0])


if __name__ == "__main__":
    unittest.main()
