#!/usr/bin/env python3
"""Check TRR-03 Tate certificates with exact, standard-library arithmetic.

Default: print a deterministic JSON receipt.  --check compares that receipt
with tate_receipt.json; --write-receipt replaces that local receipt.

The symbolic checks use Z[b,c]. Rational identities are checked by cross
multiplication, so they assert equality wherever the displayed denominators
are nonzero. The finite fixture is reported separately from those identities.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path


class Poly:
    """A sparse polynomial in b,c with integer coefficients."""

    def __init__(self, terms=0):
        if isinstance(terms, Poly):
            self.terms = terms.terms
        elif isinstance(terms, int):
            self.terms = {(0, 0): terms} if terms else {}
        else:
            self.terms = {m: int(z) for m, z in terms.items() if z}

    def __add__(self, other):
        if isinstance(other, Rat):
            return Rat(self) + other
        other = Poly(other)
        out = dict(self.terms)
        for m, z in other.terms.items():
            out[m] = out.get(m, 0) + z
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -z for m, z in self.terms.items()})

    def __sub__(self, other):
        return self + (-Rat(other) if isinstance(other, Rat) else -Poly(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if isinstance(other, Rat):
            return Rat(self) * other
        other = Poly(other)
        out = {}
        for (i, j), z in self.terms.items():
            for (k, ell), w in other.terms.items():
                m = (i + k, j + ell)
                out[m] = out.get(m, 0) + z * w
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        result, base = Poly(1), self
        while exponent:
            if exponent & 1:
                result *= base
            base *= base
            exponent //= 2
        return result

    def __truediv__(self, other):
        return Rat(self) / other

    def __rtruediv__(self, other):
        return Rat(other) / self

    def __eq__(self, other):
        if isinstance(other, Rat):
            return other == self
        return self.terms == Poly(other).terms

    def mod(self, prime):
        return Poly({m: z % prime for m, z in self.terms.items()})

    def remainder_univariate(self, divisor):
        """Exact monic univariate remainder; all current certificates use it."""
        assert all(j == 0 for i, j in self.terms)
        assert all(j == 0 for i, j in divisor.terms)
        out = self
        degree = max(i for i, j in divisor.terms)
        assert divisor.terms[(degree, 0)] == 1
        while out.terms:
            lead = max(i for i, j in out.terms)
            if lead < degree:
                break
            z = out.terms[(lead, 0)]
            out -= Poly({(lead - degree, 0): z}) * divisor
        return out


class Rat:
    """A quotient of integer polynomials; no CAS cancellation is required."""

    def __init__(self, numerator=0, denominator=1):
        if isinstance(numerator, Rat):
            assert denominator == 1
            self.n, self.d = numerator.n, numerator.d
        else:
            self.n, self.d = Poly(numerator), Poly(denominator)
        assert self.d.terms, "identically zero denominator"

    def __add__(self, other):
        other = Rat(other)
        if self.d == other.d:
            return Rat(self.n + other.n, self.d)
        return Rat(self.n * other.d + other.n * self.d, self.d * other.d)

    __radd__ = __add__

    def __neg__(self):
        return Rat(-self.n, self.d)

    def __sub__(self, other):
        return self + -Rat(other)

    def __rsub__(self, other):
        return Rat(other) - self

    def __mul__(self, other):
        other = Rat(other)
        return Rat(self.n * other.n, self.d * other.d)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Rat(other)
        assert other.n.terms, "division by identically zero function"
        return Rat(self.n * other.d, self.d * other.n)

    def __rtruediv__(self, other):
        return Rat(other) / self

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        return Rat(self.n ** exponent, self.d ** exponent)

    def __eq__(self, other):
        other = Rat(other)
        return self.n * other.d == other.n * self.d


B = Poly({(1, 0): 1})
C = Poly({(0, 1): 1})


def parse_expression(text, variables):
    """Interpret only arithmetic AST nodes; never execute certificate text."""
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return Rat(node.value)
        if isinstance(node, ast.Name) and node.id in variables:
            return Rat(variables[node.id])
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -visit(node.operand)
        if isinstance(node, ast.BinOp):
            left = visit(node.left)
            if isinstance(node.op, ast.Pow):
                assert isinstance(node.right, ast.Constant)
                assert type(node.right.value) is int and node.right.value >= 0
                return left ** node.right.value
            right = visit(node.right)
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
            if isinstance(node.op, ast.Div):
                return left / right
        raise ValueError(f"unsupported certificate syntax: {ast.dump(node)}")
    return visit(ast.parse(text, mode="eval").body)


def from_coefficients(coefficients):
    return Poly({(i, 0): z for i, z in enumerate(coefficients)})


def determinant_bareiss(matrix):
    """Integer fraction-free determinant, used for the supplied resultant."""
    a = [row[:] for row in matrix]
    n, sign, previous = len(a), 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                value = a[i][j] * pivot - a[i][k] * a[k][j]
                assert value % previous == 0
                a[i][j] = value // previous
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def resultant_univariate(left, right):
    left, right = list(reversed(left)), list(reversed(right))
    m, n = len(left) - 1, len(right) - 1
    rows = [[0] * shift + left + [0] * (n - shift - 1)
            for shift in range(n)]
    rows += [[0] * shift + right + [0] * (m - shift - 1)
             for shift in range(m)]
    return determinant_bareiss(rows)


def invariants(b, c):
    a1, a2, a3 = 1 - c, -b, -b
    b2 = a1 * a1 + 4 * a2
    b4, b6, b8 = a1 * a3, a3 * a3, a2 * a3 * a3
    delta = -b2 * b2 * b8 - 8 * b4 ** 3 - 27 * b6 ** 2 + 9 * b2 * b4 * b6
    c4 = b2 * b2 - 24 * b4
    return delta, c4


def curve_residual(point, b, c):
    """Clear x,y denominators explicitly to keep certificates small."""
    x, y = map(Rat, point)
    nx, dx, ny, dy = x.n, x.d, y.n, y.d
    return (ny ** 2 * dx ** 3 + (1 - c) * nx * ny * dx ** 2 * dy
            - b * ny * dx ** 3 * dy - nx ** 3 * dy ** 2
            + b * nx ** 2 * dx * dy ** 2)


def residues(positive_points, b, c):
    answer = []
    for i, (x, y) in enumerate(positive_points):
        denominator = 2 * y + (1 - c) * x - b
        for j, (xx, yy) in enumerate(positive_points):
            if i != j:
                denominator *= x - xx
        answer.append(1 / denominator)
    return answer


def odd_convolution(positive_x, positive_lambda):
    xs = [Poly(0)] + positive_x + list(reversed(positive_x))
    ls = [Poly(0)] + positive_lambda + [-z for z in reversed(positive_lambda)]
    n = len(xs)
    return [sum((xs[(i + j) % n] * ls[j] for j in range(n)), Poly(0))
            for i in range(1, (n + 1) // 2)]


def run_symbolic(order7, order11):
    checks = Counter()

    def check(label, left, right=0):
        assert left == right, label
        checks[label.split("/")[0]] += 1

    def check_mod(label, left, right, prime):
        check(label, (left - right).mod(prime))

    # Five-torsion, using the genuine invariant differential in Tate form.
    b = B
    points5 = [(Rat(0), Rat(0)), (Rat(b), Rat(b ** 2))]
    for i, point in enumerate(points5):
        check(f"order5/curve_{i}", curve_residual(point, b, b))
    lam5 = residues(points5, b, b)
    for i, expected in enumerate([1 / b ** 2, 1 / b ** 3]):
        check(f"order5/residue_{i}", lam5[i], expected)
    slope5 = b
    check("order5/third_x", slope5 ** 2 + (1 - b) * slope5, b)
    check("order5/third_y", b - (slope5 + 1 - b) * b, 0)
    scaled5 = [b, Poly(1)]
    image5 = odd_convolution([Poly(0), b], scaled5)
    check("order5/ratio_1", image5[0], (b + 1) * scaled5[0])
    check("order5/ratio_2", image5[1], b ** 2 * scaled5[1])
    delta5, c45 = invariants(b, b)
    check("order5/discriminant", delta5, b ** 5 * (b ** 2 - 11 * b - 1))
    exceptional = b ** 2 - b - 1
    check("order5/exception_discriminant", (delta5 + 10 * b ** 6).remainder_univariate(exceptional))
    check("order5/exception_j", (2 * c45 ** 3 + 25 * delta5).remainder_univariate(exceptional))
    # The displayed decoder is checked at all four affine points, modulo the
    # exceptional equation. These are symbolic identities, not field samples.
    full5 = [(Poly(0), Poly(0)), (b, b ** 2), (b, Poly(0)), (Poly(0), b)]
    decoder5 = [[b, -Poly(1), b - 1], [-Poly(1), b - 1, 2 * b - 3],
                [b - 1, 2 * b - 3, 2 * b - 4]]
    values5 = [b ** 2, Poly(0), b, b, Poly(0)]
    for i, (x, y) in enumerate(full5, 1):
        for j, (xx, yy) in enumerate(full5, 1):
            v, w = [Poly(1), x, y], [Poly(1), xx, yy]
            predicted = sum((v[k] * decoder5[k][ell] * w[ell]
                             for k in range(3) for ell in range(3)), Poly(0))
            check(f"order5/decoder_{i}_{j}",
                  (predicted - values5[(i + j) % 5]).remainder_univariate(exceptional))

    # Seven-torsion: derive the actual residue vector before checking ratios.
    t = B
    b7, c7 = t ** 2 * (t - 1), t * (t - 1)
    points7 = [(Rat(0), Rat(0)), (Rat(b7), Rat(b7 * c7)),
               (Rat(c7), Rat(b7 - c7))]
    for i, point in enumerate(points7):
        check(f"order7/curve_{i}", curve_residual(point, b7, c7))
    slope7 = (b7 - c7) / c7
    fourth_x = slope7 ** 2 + (1 - c7) * slope7 + b7 - c7
    fourth_y = b7 - (slope7 + 1 - c7) * fourth_x
    check("order7/fourth_x_is_third_x", fourth_x, c7)
    check("order7/fourth_y_is_negative_third_y", fourth_y, c7 ** 2)
    lam7 = residues(points7, b7, c7)
    scale = t ** 6 * (t - 1) ** 6
    scaled7 = [-t * (t - 1) ** 3, t - 1, t ** 3]
    for i in range(3):
        check(f"order7/residue_{i}", lam7[i] * scale, scaled7[i])
    image7 = odd_convolution([Poly(0), b7, c7], scaled7)
    ratios7 = [t ** 3 + t + 1, t * (3 * t ** 3 - 3 * t ** 2 + 2 * t - 1),
               (t - 1) ** 2 * (t ** 2 - 3 * t + 3)]
    for i in range(3):
        check(f"order7/ratio_{i}", image7[i], ratios7[i] * scaled7[i])
    cert = order7["order7"]
    f, h, u, v = [from_coefficients(cert[name]) for name in ("F", "H", "U", "V")]
    check("order7/ratio_difference_1", ratios7[0] - ratios7[1], -f)
    check("order7/ratio_difference_2", ratios7[1] - ratios7[2], h)
    check("order7/bezout", u * f + v * h, Poly(cert["constant"]))
    check("order7/bezout_constant", cert["constant"], 21)
    check("order7/resultant", resultant_univariate(cert["F"], cert["H"]), cert["resultant"])
    delta7, unused_c4 = invariants(b7, c7)
    expected_delta7 = t ** 7 * (t - 1) ** 7 * (t ** 3 - 8 * t ** 2 + 5 * t + 1)
    check("order7/discriminant", delta7, expected_delta7)
    check("order7/input_discriminant", delta7, from_coefficients(cert["discriminant"]))
    common = from_coefficients(cert["mod7_common_factor"])
    check("order7/input_common_factor", common, t + 2)
    check_mod("order7/mod7_F", f, 3 * common ** 4, 7)
    check_mod("order7/mod7_H", h, 2 * common ** 4, 7)
    check_mod("order7/mod7_discriminant", delta7, t ** 7 * (t - 1) ** 7 * common ** 3, 7)
    singular3 = t ** 3 + t ** 2 - t + 1
    check_mod("order7/mod3_F", f, -singular3, 3)
    check_mod("order7/mod3_H", h, -t * singular3, 3)
    check_mod("order7/mod3_discriminant", delta7, t ** 7 * (t - 1) ** 7 * singular3, 3)

    # Eleven-torsion formulas are rational identities in independent b,c;
    # this does not assert that the exceptional eigenvector locus is empty.
    b, c = B, C
    variables = {"b": b, "c": c}
    xs = [parse_expression(z, variables) for z in order11["x"]]
    ys = [parse_expression(z, variables) for z in order11["y"]]
    points11 = list(zip(xs, ys))
    for i, point in enumerate(points11):
        check(f"order11/curve_{i}", curve_residual(point, b, c))
    check("order11/first_x", xs[0], 0)
    check("order11/first_y", ys[0], 0)
    check("order11/double_x", xs[1], b)
    check("order11/double_y", ys[1], b * c)
    # For Q != +-P, the line through P=(0,0) and Q has slope y(Q)/x(Q).
    for i in range(1, 4):
        slope = ys[i] / xs[i]
        check(f"order11/add_x_{i}", xs[i + 1], slope ** 2 + (1 - c) * slope + b - xs[i])
        check(f"order11/add_y_{i}", ys[i + 1], b - (slope + 1 - c) * xs[i + 1])
    d, e = b - c ** 2 - c, b ** 2 - b * c - c ** 3
    tangent3 = (2 * c ** 2 + c - b * (c + 1)) / d
    x6 = (b - c) * e / d ** 2
    check("order11/sixth_x", x6, tangent3 ** 2 + (1 - c) * tangent3 + b - 2 * c)
    g = (b - c) ** 3 * e + b * c * d ** 3
    check("order11/order_equation", x6 - xs[4], g / ((b - c) ** 2 * d ** 2))
    for name in ("order11_relation", "order11_relation_expanded"):
        check(f"order11/{name}", parse_expression(order11[name], variables), g)
    actual_lam11 = residues(points11, b, c)
    for i, text in enumerate(order11["lambda"]):
        check(f"order11/residue_{i}", parse_expression(text, variables), actual_lam11[i])
    delta11, unused_c4 = invariants(b, c)
    check("order11/discriminant", delta11,
          b ** 3 * (16 * b ** 2 - 8 * b * c ** 2 - 20 * b * c + b
                     + c ** 4 - 3 * c ** 3 + 3 * c ** 2 - c))
    return dict(sorted(checks.items()))


def tate_add(left, right, b, c, prime):
    if left is None:
        return right
    if right is None:
        return left
    x, y = left
    xx, yy = right
    a1, a2, a3 = 1 - c, -b, -b
    if x == xx and (y + yy + a1 * x + a3) % prime == 0:
        return None
    if x == xx:
        slope = (3 * x * x + 2 * a2 * x - a1 * y) * pow(2 * y + a1 * x + a3, -1, prime) % prime
    else:
        slope = (yy - y) * pow(xx - x, -1, prime) % prime
    intercept = (y - slope * x) % prime
    xxx = (slope * slope + a1 * slope - a2 - x - xx) % prime
    yyy = (-(slope + a1) * xxx - intercept - a3) % prime
    return xxx, yyy


def rank_mod(matrix, prime):
    a = [[z % prime for z in row] for row in matrix]
    rank, width = 0, len(a[0])
    for column in range(width):
        pivot = next((i for i in range(rank, len(a)) if a[i][column]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][column], -1, prime)
        a[rank] = [z * inv % prime for z in a[rank]]
        for i in range(rank + 1, len(a)):
            factor = a[i][column]
            a[i] = [(z - factor * w) % prime for z, w in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def run_finite_fixture():
    count = 0

    def check(label, condition):
        nonlocal count
        assert condition, label
        count += 1

    p, b, c = 23, 1, 5
    points = [None]
    current = None
    for _ in range(11):
        current = tate_add(current, (0, 0), b, c, p)
        points.append(current)
    check("order_exactly_eleven", points[-1] is None and len(set(points[:-1])) == 11)
    group = points[:-1]
    expected_points = [(0, 0), (1, 5), (5, 19), (21, 19), (22, 22)]
    check("positive_points", group[1:6] == expected_points)
    for point in group[1:]:
        x, y = point
        check("on_curve", (y*y + (1-c)*x*y - b*y - x*x*x + b*x*x) % p == 0)
    for i in range(11):
        for j in range(11):
            check("addition_table", tate_add(group[i], group[j], b, c, p) == group[(i+j) % 11])
    d, e = (b-c*c-c) % p, (b*b-b*c-c**3) % p
    delta = b**3 * (16*b*b-8*b*c*c-20*b*c+b+c**4-3*c**3+3*c*c-c) % p
    check("d_e_delta", (d, e, delta) == (17, 9, 14))
    check("order_equation", ((b-c)**3*e+b*c*d**3) % p == 0)
    lam = []
    for i in range(1, 6):
        x, y = group[i]
        denominator = (2*y+(1-c)*x-b) % p
        for j in range(1, 6):
            if i != j:
                denominator = denominator * (x-group[j][0]) % p
        lam.append(pow(denominator, -1, p))
    check("residue_vector", lam == [16, 9, 15, 6, 21])
    full_lam = [0] + lam + [(-z) % p for z in reversed(lam)]
    values = [0] + [point[0] for point in group[1:]]
    ratios = [sum(values[(i+j) % 11]*full_lam[j] for j in range(11))
              * pow(full_lam[i], -1, p) % p for i in range(1, 6)]
    check("ratios", ratios == [13, 8, 0, 19, 2])
    check("every_pole_assignment_rejected", len(set(ratios)) > 1)
    feature_ranks = {}
    for degree in (3, 4):
        monomials = [(i, j) for i in range(degree+1) for j in range(degree+1-i)]
        features = [[pow(x, i, p)*pow(y, j, p) % p for i, j in monomials]
                    for x, y in group[1:]]
        feature_ranks[str(degree)] = rank_mod(features, p)
    check("feature_ranks", feature_ranks == {"3": 9, "4": 10})
    return {"assertions": count, "field": p, "tate_b": b, "tate_c": c,
            "subgroup_order": 11, "discriminant": delta,
            "positive_points": [list(point) for point in expected_points], "positive_residues": lam,
            "positive_ratios": ratios, "feature_ranks": feature_ranks,
            "minimum_separate_decoder_degree_for_every_pole_value": 4,
            "addition_table_pairs_checked": 121}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write-receipt", action="store_true")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    names = ["order7_certificate.json", "order11_system.json"]
    inputs = {name: (here / name).read_bytes() for name in names}
    exact = run_symbolic(*(json.loads(inputs[name]) for name in names))
    receipt = {
        "schema": "trr03-tate-certificates-v1",
        "arithmetic": "sparse integer polynomials and cross-multiplied rational functions; standard library only",
        "source_sha256": {name: hashlib.sha256(data).hexdigest() for name, data in sorted(inputs.items())},
        "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "exact_identity_assertions": sum(exact.values()),
        "exact_identity_assertions_by_family": exact,
        "finite_fixture": run_finite_fixture(),
        "order11_exceptional_locus_status": "unresolved; symbolic setup and one nonexceptional fixture verified",
    }
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    receipt_path = here / "tate_receipt.json"
    if args.check:
        assert json.loads(receipt_path.read_text()) == receipt, "receipt differs"
    elif args.write_receipt:
        receipt_path.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
