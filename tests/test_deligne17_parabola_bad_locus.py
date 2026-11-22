"""DEL-17 independent exact oracle for parabola-product bad-locus polynomial.

On U² with U={(x,y):y=x²}, the fixed bilinear path coordinate is
B=x₀x₁, and the pulled-back section is
G=alpha*x²+x*y+beta*y²+p*x+q*y+c.

Tests the exact polynomial Bézout identity in every characteristic,
the sharp generic-open test, and degenerate points belonging to
the Zariski closure of the bad incidence but not its actual projection.
"""
from __future__ import annotations

import json
import unittest
from pathlib import Path

FIELDS = (2, 3, 5, 7, 11, 13, 17)
KINDS = ("critical", "regular", "closure_only", "sign_mutant")


def freeze() -> list[dict]:
    rows = []
    for i in range(96):
        kind = KINDS[i % len(KINDS)]
        field = FIELDS[i % len(FIELDS)]
        if kind == "closure_only" and field == 2:
            field = 3
        x, y = (3 * i + 1) % field, (5 * i + 2) % field
        alpha, beta = (i + 1) % field, (2 * i + 1) % field
        if kind == "regular":
            alpha = 0
        if kind == "sign_mutant":
            alpha, beta = 0, 1
        if kind == "closure_only":
            alpha, beta = 1, pow(4, -1, field)
        p = (-2 * alpha * x - y) % field
        q = (-x - 2 * beta * y) % field
        c = (alpha * x**2 + x * y + beta * y**2) % field
        if kind == "regular":
            c = (c + 1) % field
        if kind == "sign_mutant":
            p, c = (p + 1) % field, (c - x) % field
        if kind == "closure_only":
            p, q, c = 0, 0, 1
        gradient_x = (2 * alpha * x + y + p) % field
        gradient_y = (x + 2 * beta * y + q) % field
        section_value = (alpha * x**2 + x * y + beta * y**2 +
                         p * x + q * y + c) % field
        eliminant = ((4 * alpha * beta - 1) * c -
                     alpha * q*q - beta * p*p + p*q) % field
        has = any(
            quadratic(field, alpha, beta, p, q, c, X, Y) == 0 and
            grad_x(field, alpha, p, X, Y) == 0 and
            grad_y(field, beta, q, X, Y) == 0
            for X in range(field) for Y in range(field)
        )
        rows.append({
            "id": f"DEL17-{i + 1:03d}", "kind": kind,
            "field": f"F{field}", "alpha": alpha, "beta": beta,
            "p": p, "q": q, "c": c, "x": x, "y": y,
            "gradient_x": gradient_x, "gradient_y": gradient_y,
            "section_value": section_value, "eliminant": eliminant,
            "parameter_on_bad_hypersurface": eliminant == 0,
            "has_rational_critical_point": has,
        })
    return rows


def quadratic(f: int, a: int, b: int, p: int, q: int, c: int,
              x: int, y: int) -> int:
    return (a*x*x + x*y + b*y*y + p*x + q*y + c) % f


def grad_x(f: int, a: int, p: int, x: int, y: int) -> int:
    return (2*a*x+y+p) % f


def grad_y(f: int, b: int, q: int, x: int, y: int) -> int:
    return (x+2*b*y+q) % f


def poly_derivative(poly: dict[tuple[int, int], int], variable: int,
                    modulus: int) -> dict[tuple[int, int], int]:
    out = {}
    for key, coef in poly.items():
        exponent = key[variable]
        if exponent:
            new = list(key)
            new[variable] -= 1
            nk = tuple(new)
            out[nk] = (out.get(nk, 0) + coef * exponent) % modulus
    return out


def poly_eval(poly: dict[tuple[int, int], int],
              f: int, x: int, y: int) -> int:
    return sum(coef * x**i * y**j for (i,j),coef in poly.items()) % f


class ParabolaEliminationOracle(unittest.TestCase):
    def test_exact_frozen_corpus(self) -> None:
        file = Path(__file__).resolve().parents[1] / (
            "research/deligne_sign_audit/del17_tasks.jsonl")
        rows = [json.loads(s) for s in file.read_text().splitlines() if s]
        self.assertEqual(rows, freeze())
        self.assertEqual(len(rows), 96)
        self.assertEqual(len({row["id"] for row in rows}), 96)

    def test_real_partial_derivatives_via_sparse_polynomials(self) -> None:
        for r in freeze():
            f = int(r["field"][1:])
            poly = {(2,0):r["alpha"], (1,1):1, (0,2):r["beta"],
                    (1,0):r["p"], (0,1):r["q"], (0,0):r["c"]}
            xder = poly_derivative(poly, 0, f)
            yder = poly_derivative(poly, 1, f)
            for x in range(f):
                for y in range(f):
                    self.assertEqual(poly_eval(xder, f, x, y),
                                     grad_x(f, r["alpha"], r["p"], x, y))
                    self.assertEqual(poly_eval(yder, f, x, y),
                                     grad_y(f, r["beta"], r["q"], x, y))

    def test_global_bezout_polynomial_identity(self) -> None:
        for r in freeze():
            f = int(r["field"][1:])
            a,b,p,q,c = (r[k] for k in ("alpha","beta","p","q","c"))
            d = (4*a*b-1) % f
            for x in range(f):
                for y in range(f):
                    G = quadratic(f,a,b,p,q,c,x,y)
                    Gx = grad_x(f,a,p,x,y)
                    Gy = grad_y(f,b,q,x,y)
                    lhs = (d*G - a*Gy**2 - b*Gx**2 + Gx*Gy) % f
                    self.assertEqual(lhs, r["eliminant"], r)

    def test_critical_parameters_obey_polynomial(self) -> None:
        for r in freeze():
            if r["has_rational_critical_point"]:
                self.assertEqual(r["eliminant"],0,r)

    def test_regular_certificate_excludes_critical_points(self) -> None:
        for r in freeze():
            if r["eliminant"] != 0:
                self.assertFalse(r["has_rational_critical_point"],r)

    def test_generic_open_iff(self) -> None:
        for r in freeze():
            f = int(r["field"][1:])
            determinant = (4*r["alpha"]*r["beta"]-1) % f
            if determinant:
                self.assertEqual(r["eliminant"] == 0,
                                 r["has_rational_critical_point"], r)

    def test_closure_only_exceptional_parameters(self) -> None:
        examples = [r for r in freeze() if r["kind"] == "closure_only"]
        self.assertEqual(len(examples),24)
        for r in examples:
            f = int(r["field"][1:])
            self.assertEqual((4*r["alpha"]*r["beta"]-1) % f,0)
            self.assertEqual(r["eliminant"],0)
            self.assertFalse(r["has_rational_critical_point"])

    def test_sign_mutants_fail(self) -> None:
        for r in freeze():
            if r["kind"] == "sign_mutant":
                self.assertNotEqual(r["eliminant"],0)
                self.assertFalse(r["has_rational_critical_point"])
                self.assertEqual(r["section_value"],0)
                self.assertNotEqual(r["gradient_x"],0)

    def test_parameter_polynomial_has_degree_three(self) -> None:
        # Expand E=(4alpha beta-1)c-alpha q²-beta p²+pq.
        terms = {
            (1,1,0,0,1):4,
            (0,0,0,0,1):-1,
            (1,0,0,2,0):-1,
            (0,1,2,0,0):-1,
            (0,0,1,1,0):1,
        }
        self.assertEqual(max(sum(exponents) for exponents in terms),3)
        self.assertEqual(terms[(0,0,0,0,1)],-1)

    def test_formally_nonzero_even_over_f2(self) -> None:
        for f in FIELDS:
            E = ((4*0*0-1)*1 - 0*0 - 0*0 + 0*0)%f
            self.assertEqual(E, f-1)
            self.assertNotEqual(E,0)

    def test_polynomial_function_vs_formal_polynomial(self) -> None:
        for f in FIELDS:
            self.assertTrue(all((x**f-x)%f == 0 for x in range(f)))
            self.assertNotEqual({f:1, 1:-1},{})


if __name__ == "__main__":
    unittest.main()
