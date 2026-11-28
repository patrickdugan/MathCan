"""DEL-15 exact finite-field oracle for a relative embedded-line Jacobian.

No symbolic-algebra dependency. Polynomial gcd uses an independent
Euclidean algorithm over prime fields and checks the actual derivative.
"""
from __future__ import annotations

import json
import unittest
from pathlib import Path

PRIMES = (2, 3, 5, 7, 11, 13, 17)


def section(p: int, a: int, b: int, c: int, d: int, x: int) -> int:
    return (x * x + (d + a + b) * x + b * d + c) % p


def derivative(p: int, a: int, b: int, c: int, d: int, x: int) -> int:
    return (2 * x + d + a + b) % p


def restricted_delta(p: int, a: int, b: int, c: int, d: int) -> int:
    return ((d + a + b) ** 2 - 4 * (b * d + c)) % p


def ambient_delta(p: int, a: int, b: int, c: int) -> int:
    return (c - a * b) % p


def trim(f: list[int], p: int) -> list[int]:
    h = [x % p for x in f]
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def remainder(f: list[int], g: list[int], p: int) -> list[int]:
    f, g = trim(f, p), trim(g, p)
    if g == [0]:
        raise ZeroDivisionError("zero polynomial")
    lead_inverse = pow(g[-1], -1, p)
    while f != [0] and len(f) >= len(g):
        coef = f[-1] * lead_inverse % p
        shift = len(f) - len(g)
        for j, gj in enumerate(g):
            f[shift + j] = (f[shift + j] - coef * gj) % p
        f = trim(f, p)
    return f


def gcd_degree(f: list[int], g: list[int], p: int) -> int:
    f, g = trim(f, p), trim(g, p)
    while g != [0]:
        f, g = g, remainder(f, g, p)
    return len(f) - 1


def exact_task_rows() -> list[dict]:
    """Deterministic and balanced, including characteristic two and mutations."""
    rows = []
    kinds = ("regular", "critical", "tangent", "ambient_mutant")
    for i in range(96):
        p = PRIMES[i % len(PRIMES)]
        a = (11 * i + 3) % p
        b = (i * i + 2) % p
        d = (5 * i + 1) % p
        c = (7 * i + 4) % p
        kind = kinds[i % 4]
        if kind == "tangent":
            a, b, c, d = 0, 0, 1 % p, (-2) % p
        elif kind == "critical":
            if p == 2:
                d = (-a - b) % p
            else:
                c = ((d + a + b) ** 2 * pow(4, -1, p) - b * d) % p
        elif kind == "regular":
            if p == 2 and (d + a + b) % p == 0:
                a = (a + 1) % p
            else:
                while restricted_delta(p, a, b, c, d) == 0:
                    c = (c + 1) % p
        elif kind == "ambient_mutant":
            # Ambient regularity does not imply relative regularity.
            a, b, c, d = 0, 0, 1 % p, (-2) % p
        delta = restricted_delta(p, a, b, c, d)
        rows.append({
            "id": f"DEL15-{i + 1:03d}",
            "kind": kind, "field": f"F{p}",
            "a": a, "b": b, "c": c, "d": d,
            "relative_discriminant": delta,
            "ambient_discriminant": ambient_delta(p, a, b, c),
            "critical": delta == 0,
            "source": "actual restricted conic and polynomial formal derivative",
        })
    return rows


class EmbeddedLineOracle(unittest.TestCase):
    def test_exact_96_corpus(self) -> None:
        path = Path(__file__).resolve().parents[1] / (
            "research/deligne_sign_audit/del15_tasks.jsonl")
        rows = [json.loads(x) for x in path.read_text().splitlines() if x.strip()]
        self.assertEqual(rows, exact_task_rows())
        self.assertEqual(len(rows), 96)
        self.assertEqual({row["kind"] for row in rows},
                         {"regular", "critical", "tangent", "ambient_mutant"})
        self.assertEqual(len({row["id"] for row in rows}), 96)

    def test_pointwise_restriction(self) -> None:
        for p in PRIMES:
            for a in range(p):
                for b in range(min(p, 4)):
                    for x in range(p):
                        d, c = (a + 2) % p, (b + 1) % p
                        y = (x + d) % p
                        ambient = (x * y + a * x + b * y + c) % p
                        self.assertEqual(section(p, a, b, c, d, x), ambient)

    def test_chain_rule_relative_derivative(self) -> None:
        for p in PRIMES:
            for row in exact_task_rows():
                a, b, c, d = (row[key] % p for key in ("a", "b", "c", "d"))
                for x in range(p):
                    y = (x + d) % p
                    # dF/dx + dF/dy along the tangent vector (1,1).
                    tangential = (y + a + x + b) % p
                    self.assertEqual(derivative(p, a, b, c, d, x), tangential)

    def test_bezout_identity_at_all_points(self) -> None:
        for p in PRIMES:
            for row in exact_task_rows():
                a, b, c, d = (row[key] % p for key in ("a", "b", "c", "d"))
                delta = restricted_delta(p, a, b, c, d)
                for x in range(p):
                    self.assertEqual(
                        (derivative(p, a, b, c, d, x) ** 2 -
                         4 * section(p, a, b, c, d, x)) % p,
                        delta,
                    )

    def test_euclidean_jacobian_ideal(self) -> None:
        for p in PRIMES:
            for row in exact_task_rows():
                a, b, c, d = (row[key] % p for key in ("a", "b", "c", "d"))
                g = [(b * d + c) % p, (d + a + b) % p, 1]
                dg = [(d + a + b) % p, 2 % p]
                self.assertEqual(
                    gcd_degree(g, dg, p) == 0,
                    restricted_delta(p, a, b, c, d) != 0,
                    (p, row),
                )

    def test_base_field_critical_point_oracle(self) -> None:
        for row in exact_task_rows():
            p = int(row["field"][1:])
            a, b, c, d = (row[key] for key in ("a", "b", "c", "d"))
            critical = any(section(p, a, b, c, d, x) == 0 and
                           derivative(p, a, b, c, d, x) == 0
                           for x in range(p))
            self.assertEqual(critical, row["critical"], row)

    def test_tangent_counterexample_in_every_characteristic(self) -> None:
        for p in PRIMES:
            a, b, c, d = 0, 0, 1 % p, (-2) % p
            self.assertEqual(ambient_delta(p, a, b, c), 1 % p)
            self.assertEqual(restricted_delta(p, a, b, c, d), 0)
            self.assertEqual(section(p, a, b, c, d, 1 % p), 0)
            self.assertEqual(derivative(p, a, b, c, d, 1 % p), 0)
            # One ambient partial is 1 at (1,-1), so it is nonzero.
            self.assertEqual((1 + b) % p, 1 % p)

    def test_bad_locus_is_proper(self) -> None:
        for p in PRIMES:
            self.assertEqual(restricted_delta(p, 1, 0, 0, 0), 1 % p)

    def test_wrong_ambient_discriminant_is_rejected(self) -> None:
        for p in PRIMES:
            self.assertNotEqual(
                ambient_delta(p, 0, 0, 1),
                restricted_delta(p, 0, 0, 1, (-2) % p),
            )

    def test_characteristic_two_derivative(self) -> None:
        p = 2
        for a in range(2):
            for b in range(2):
                for c in range(2):
                    for d in range(2):
                        delta = restricted_delta(p, a, b, c, d)
                        slope = (d + a + b) % p
                        self.assertEqual(delta, slope)
                        for x in range(2):
                            self.assertEqual(derivative(p, a, b, c, d, x), slope)

    def test_sufficient_good_open_over_finite_fields(self) -> None:
        # For each Fp the point a=1,b=c=d=0 lies in D(Delta).
        for p in PRIMES:
            self.assertEqual(restricted_delta(p, 1, 0, 0, 0), 1)
            self.assertTrue(all(
                section(p, 1, 0, 0, 0, x) != 0 or
                derivative(p, 1, 0, 0, 0, x) != 0
                for x in range(p)
            ))


if __name__ == "__main__":
    unittest.main()
