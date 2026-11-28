"""Witnesses and mutants for finite shadows of Lemmas 2/3 and Proposition 4."""
import random
import unittest

from research.deligne_sign_audit.check import (
    all_unit_weights,
    hyperbola_sign_receipt,
    vectors,
    verify_fourier_orthogonality,
    verify_path_bound,
)


class DeligneSignAudit(unittest.TestCase):
    def test_fourier_exact_orthogonality(self):
        for p, d in ((2, 1), (2, 2), (3, 1), (3, 2)):
            with self.subTest(p=p, d=d):
                self.assertTrue(verify_fourier_orthogonality(p, d))
        self.assertTrue(verify_fourier_orthogonality(3, 2, ((0, 1), (1, 0))))

    def test_character_path_lemma_exact_square(self):
        rng = random.Random(261100789)
        for p, d, ks in ((2, 1, (2, 3, 4, 5, 6)),
                         (3, 1, (2, 3, 4, 5)),
                         (2, 2, (2, 3, 4)),
                         (3, 2, (2, 3))):
            space = vectors(p, d)
            for k in ks:
                for _ in range(12):
                    weights = tuple({x: rng.randrange(-2, 3) for x in space}
                                    for _ in range(k))
                    receipt = verify_path_bound(p, d, weights)
                    self.assertTrue(receipt["ok"], (p, d, k, receipt))

    def test_degenerate_bilinear_mutation_rejected(self):
        p, d, k = 2, 1, 3
        weights = all_unit_weights(p, d, k)
        bad = verify_path_bound(p, d, weights, ((0,),))
        self.assertFalse(bad["ok"])
        self.assertEqual(bad["norm2"], 64)
        self.assertEqual(bad["ceiling"], 16)
        self.assertFalse(verify_fourier_orthogonality(p, d, ((0,),)))

    def test_exact_conic_sign_and_singularity_mutation(self):
        for p in (2, 3, 5, 7, 11):
            a, b, c = 1, 1, 0
            receipt = hyperbola_sign_receipt(p, a, b, c)
            self.assertTrue(receipt["smooth"])
            self.assertEqual(receipt["N"], p - 1)
            self.assertEqual(receipt["R"], -p)
            self.assertEqual(receipt["signedR"], p)
            mutant = hyperbola_sign_receipt(p, a, b, a * b)
            self.assertFalse(mutant["smooth"])
            self.assertEqual(mutant["N"], 2 * p - 1)
            self.assertNotEqual(mutant["signedR"], p)

    def test_power_sum_positivity_mutation(self):
        # Opposite coefficients on the same eigenvalue hide arbitrary growth.
        for lam in (2, 7, 101):
            for n in range(1, 9):
                self.assertEqual(lam**n - lam**n, 0)
        # A finite n=1 trace check misses the even-power growth.
        self.assertEqual(7 + (-7), 0)
        self.assertGreater(7**2 + (-7)**2, 0)


if __name__ == "__main__":
    unittest.main()
