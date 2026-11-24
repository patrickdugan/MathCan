"""CLN-01 exact finite orbit regressions; no floating-point arithmetic."""
from collections import Counter
from math import gcd, prod
import unittest


def valuation(n, p):
    if n == 0 or p < 2:
        raise ValueError("nonzero integer and prime required")
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def prime_factors(q):
    return [p for p in range(2, q + 1) if q % p == 0
            and all(p % d for d in range(2, p))]


def order(b, m):
    if gcd(b, m) != 1:
        raise ValueError("base must be a unit")
    if m == 1:
        return 1
    x = b % m
    p = 1
    while x != 1:
        x = x * b % m
        p += 1
        if p > m:
            raise AssertionError("order exceeded modulus")
    return p


def period_data(q, k, b, h):
    if q < 2 or k < 1 or b < 2 or h == 0 or gcd(b, q) != 1:
        raise ValueError("invalid coprime orbit parameters")
    m = q ** k
    p = order(b, m // gcd(abs(h), m))
    factors = [(ell, valuation(h, ell),
                valuation(b ** (2 if ell == 2 else ell - 1) - 1, ell))
               for ell in prime_factors(q)]
    divisor = prod(ell ** max(k * valuation(q, ell) - v - c, 0)
                   for ell, v, c in factors)
    bound = prod(ell ** (v + c) for ell, v, c in factors)
    return m, p, divisor, bound


def collision_count(n, p):
    u, r = divmod(n, p)
    return p * u * u + r * (2 * u + 1)


def residues(b, m, h, n):
    out = []
    a = h % m
    for _ in range(n):
        out.append(a)
        a = a * b % m
    return out


class CantorPrefixEntropyTests(unittest.TestCase):
    def test_period_and_exact_collision_bound(self):
        cases = 0
        for q in range(2, 13):
            for b in range(2, 16):
                if gcd(q, b) != 1:
                    continue
                for k in range(1, 4):
                    for h in (-12, -3, 1, 2, 9, 25):
                        m, p, d, K = period_data(q, k, b, h)
                        self.assertEqual(p % d, 0)
                        self.assertLessEqual(m, K * p)
                        for n in (m, m + 1, 2 * m - 1):
                            counts = Counter(residues(b, m, h, n))
                            C = sum(x * x for x in counts.values())
                            self.assertEqual(C, collision_count(n, p))
                            self.assertLessEqual(C * p, n * (p + n))
                            self.assertLessEqual(m * C, (1 + K) * n * n)
                        cases += 1
        self.assertGreater(cases, 1000)

    def test_weighted_collision_energy(self):
        # Integer real/imaginary pairs represent fourth roots of unity.
        phases = [(1, 0), (0, 1), (-1, 0), (0, -1)]
        for q, b, h in ((3, 2, 1), (3, 10, 3), (6, 5, -2), (4, 3, 4)):
            m, p, _, _ = period_data(q, 2, b, h)
            a = residues(b, m, h, 2 * m - 1)
            for mode in range(5):
                w = [phases[(i * i + mode * i + mode) % 4]
                     for i in range(len(a))]
                sums = {}
                for x, (re, im) in zip(a, w):
                    u, v = sums.get(x, (0, 0))
                    sums[x] = u + re, v + im
                energy = sum(re * re + im * im for re, im in sums.values())
                pair_sum = sum(w[i][0] * w[j][0] + w[i][1] * w[j][1]
                               for i in range(len(a)) for j in range(len(a))
                               if a[i] == a[j])
                self.assertEqual(energy, pair_sum)
                self.assertLessEqual(energy, collision_count(len(a), p))

    def test_ternary_order_formula_and_nonunit_controls(self):
        for b in range(2, 20):
            if b % 3 == 0:
                with self.assertRaises(ValueError):
                    period_data(3, 2, b, 1)
                continue
            d = order(b, 3)
            c = valuation(b ** d - 1, 3)
            for t in range(1, 8):
                self.assertEqual(order(b, 3 ** t), d * 3 ** max(t - c, 0))
        with self.assertRaises(ValueError):
            period_data(3, 2, 2, 0)
        self.assertEqual(order(2, 1), 1)

    def test_interpolation_grid_covers_each_integer(self):
        for q in range(2, 8):
            for k in range(1, 4):
                m = q ** k
                for J in range(1, 12):
                    grid = [m + j * m // J for j in range((q - 1) * J + 1)]
                    self.assertEqual(grid[0], m)
                    self.assertEqual(grid[-1], q * m)
                    self.assertTrue(all(J * (v - u) <= m + J
                                        for u, v in zip(grid, grid[1:])))
                    for n in range(m, q * m):
                        left = max(x for x in grid if x <= n)
                        self.assertLessEqual(J * (n - left), m + J)


if __name__ == "__main__":
    unittest.main()
