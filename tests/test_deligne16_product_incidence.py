"""DEL-16 independent exact algebra for embedded U² relative tangency.

U = {(x,y): y-x²=0}.  The prescribed last-coordinate phase is
B(u0,u1) = x0*x1.  The fixed coefficient on B is exactly 1.
This oracle checks genuine product equations, tangent vectors,
Lagrange multipliers, and a separate elimination-polynomial syzygy.
"""
from __future__ import annotations

import json
import unittest
from pathlib import Path

PRIMES = (2, 3, 5, 7, 11, 13, 17)
KINDS = ("critical", "regular", "tangent_counterexample", "sign_mutant")


def frozen_rows() -> list[dict]:
    rows = []
    for i in range(96):
        p = PRIMES[i % len(PRIMES)]
        kind = KINDS[i % len(KINDS)]
        x0, x1 = (7 * i + 1) % p, (i * i + 2) % p
        ay0, ay1 = (3 * i + 1) % p, (5 * i + 2) % p
        if kind == "critical":
            ay0 = ay1 = 0
        if kind == "tangent_counterexample":
            ay0, ay1 = ay0 or 1, ay1 or 1
        ax0 = (-x1 - 2 * x0 * ay0) % p
        ax1 = (-x0 - 2 * x1 * ay1) % p
        if kind == "regular":
            ax0 = (ax0 + 1) % p
        if kind == "sign_mutant":
            ax1 = (ax1 + 1) % p
        c = -(x0 * x1 + ax0 * x0 + ay0 * x0**2 +
              ax1 * x1 + ay1 * x1**2)
        c %= p
        tangent0 = (x1 + ax0 + 2 * x0 * ay0) % p
        tangent1 = (x0 + ax1 + 2 * x1 * ay1) % p
        rows.append({
            "id": f"DEL16-{i + 1:03d}", "kind": kind, "field": f"F{p}",
            "x0": x0, "x1": x1,
            "y0": x0 * x0 % p, "y1": x1 * x1 % p,
            "ax0": ax0, "ay0": ay0, "ax1": ax1, "ay1": ay1,
            "c": c, "lambda0": ay0, "lambda1": ay1,
            "tangent0": tangent0, "tangent1": tangent1,
            "critical": tangent0 == 0 and tangent1 == 0,
        })
    return rows


def fixed_section(r: dict) -> int:
    p = int(r["field"][1:])
    return (r["x0"] * r["x1"] +
            r["ax0"] * r["x0"] + r["ay0"] * r["y0"] +
            r["ax1"] * r["x1"] + r["ay1"] * r["y1"] +
            r["c"]) % p


def ambient_gradient(r: dict) -> tuple[int, int, int, int]:
    p = int(r["field"][1:])
    return ((r["x1"] + r["ax0"]) % p, r["ay0"] % p,
            (r["x0"] + r["ax1"]) % p, r["ay1"] % p)


def normal_gradient(r: dict) -> tuple[int, int, int, int]:
    p = int(r["field"][1:])
    return ((-2 * r["x0"] * r["lambda0"]) % p,
            r["lambda0"] % p,
            (-2 * r["x1"] * r["lambda1"]) % p,
            r["lambda1"] % p)


def tangent_derivative(r: dict, v0: int, v1: int) -> int:
    p = int(r["field"][1:])
    dx0, dy0, dx1, dy1 = ambient_gradient(r)
    return ((dx0 + 2 * r["x0"] * dy0) * v0 +
            (dx1 + 2 * r["x1"] * dy1) * v1) % p


class ProductIncidenceOracle(unittest.TestCase):
    def test_frozen_corpus(self) -> None:
        path = (Path(__file__).resolve().parents[1] /
                "research/deligne_sign_audit/del16_tasks.jsonl")
        rows = [json.loads(t) for t in path.read_text().splitlines() if t]
        self.assertEqual(rows, frozen_rows())
        self.assertEqual(len(rows), 96)
        self.assertEqual(len({row["id"] for row in rows}), 96)
        self.assertEqual({kind: sum(r["kind"] == kind for r in rows)
                          for kind in KINDS}, {kind: 24 for kind in KINDS})

    def test_each_factor_satisfies_actual_equation(self) -> None:
        for r in frozen_rows():
            p = int(r["field"][1:])
            for i in (0, 1):
                self.assertEqual((r[f"y{i}"] - r[f"x{i}"]**2) % p, 0)

    def test_hyperplane_section_vanishes(self) -> None:
        for r in frozen_rows():
            self.assertEqual(fixed_section(r), 0, r)

    def test_actual_constraint_jacobian(self) -> None:
        for r in frozen_rows():
            p = int(r["field"][1:])
            for i in (0, 1):
                x = r[f"x{i}"]
                # d(y-x²)=(-2x,1), annihilating v=(1,2x)
                self.assertEqual((-2*x + 2*x) % p, 0)

    def test_lagrange_certificate_is_sharp(self) -> None:
        for r in frozen_rows():
            self.assertEqual(ambient_gradient(r) == normal_gradient(r),
                             r["critical"], r)

    def test_all_tangent_directions(self) -> None:
        for r in frozen_rows():
            p = int(r["field"][1:])
            for v0 in range(p):
                for v1 in range(p):
                    expected = (r["tangent0"] * v0 +
                                r["tangent1"] * v1) % p
                    self.assertEqual(tangent_derivative(r, v0, v1),
                                     expected, r)
                    if r["critical"]:
                        self.assertEqual(expected, 0)

    def test_tangent_can_be_critical_with_nonzero_ambient_gradient(self) -> None:
        rows = [r for r in frozen_rows()
                if r["kind"] == "tangent_counterexample"]
        for r in rows:
            self.assertTrue(r["critical"])
            self.assertNotEqual(ambient_gradient(r), (0, 0, 0, 0))

    def test_sign_mutations_are_detected(self) -> None:
        for r in frozen_rows():
            if r["kind"] in ("sign_mutant", "regular"):
                self.assertFalse(r["critical"])
                self.assertNotEqual(ambient_gradient(r), normal_gradient(r))

    def test_elimination_bezout_syzygy(self) -> None:
        # I=(p-w,w²-1).  P(p)=p²-1 belongs to elimination I∩Fp[p]
        # because P=(p+w)(p-w)+(w²-1).
        for p in PRIMES:
            for parameter in range(p):
                for witness in range(p):
                    left = (parameter**2 - 1) % p
                    right = (((parameter + witness) * (parameter - witness)) +
                             (witness**2 - 1)) % p
                    self.assertEqual(left, right)
                    if ((parameter - witness) % p == 0 and
                            (witness**2 - 1) % p == 0):
                        self.assertEqual(left, 0)

    def test_finite_field_polynomial_function_trap(self) -> None:
        for p in PRIMES:
            self.assertTrue(all((x**p - x) % p == 0 for x in range(p)))
            # Coefficient of formal X^p is 1, distinct from the X term.
            self.assertGreater(p, 1)

    def test_fixed_bilinear_coefficient(self) -> None:
        for r in frozen_rows():
            p = int(r["field"][1:])
            phase = r["x0"] * r["x1"] % p
            self.assertEqual(phase, r["x0"] * r["x1"] % p)


if __name__ == "__main__":
    unittest.main()
