"""Exact finite controls for the CLN-05 composite-modulus proof."""
from math import gcd
import unittest


def order(b, m):
    assert gcd(b, m) == 1
    if m == 1:
        return 1
    a, p = b % m, 1
    while a != 1:
        a, p = a * b % m, p + 1
    return p


class CompositePeriodTests(unittest.TestCase):
    def test_fixed_constant(self):
        cases = 0
        for Q in range(2, 13):
            for b in range(2, 16):
                if gcd(Q, b) != 1:
                    continue
                z = b ** order(b, Q)
                for k in range(4):
                    M = Q ** k
                    for h in (1, 2, 3, 9, 12, 25):
                        P = order(b, M // gcd(M, h))
                        self.assertEqual((h * (z*z-1) * P) % M, 0)
                        cases += 1
        self.assertEqual(cases, 2112)

    def test_dependent_prefix_tail(self):
        # Uniform A, but the tail T=A/M**2 identifies the prefix A.
        # Marginal max-mass is 1/M, conditional max-mass is 1.
        from collections import Counter, defaultdict
        from fractions import Fraction
        for M in (3, 9, 27, 81):
            prefixes = Counter()
            by_tail = defaultdict(Counter)
            for a in range(M):
                t = Fraction(a, M*M)
                self.assertLess(t, Fraction(1, M))
                prefixes[a] += 1
                by_tail[t][a] += 1
            self.assertEqual(Fraction(max(prefixes.values()), M),
                             Fraction(1, M))
            self.assertEqual(max(Fraction(max(c.values()), sum(c.values()))
                                 for c in by_tail.values()), 1)


if __name__ == "__main__":
    unittest.main()
