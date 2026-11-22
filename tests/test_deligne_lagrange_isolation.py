"""DEL-04: executable rational shadow of Lagrange spectral extraction."""
import random
import unittest
from fractions import Fraction as Q
from research.deligne_sign_audit.power_sum_poles import spectrum, power_trace
from research.deligne_sign_audit.lagrange_isolation import (
    polynomial_mul_linear, polynomial_eval, isolating_polynomial,
    isolator_identity, isolation_certificate, scalar_geometric_counterexample
)


class LagrangeIsolatorTests(unittest.TestCase):
    def test_single_eigenvalue(self):
        self.assertEqual(isolating_polynomial([(7, 4)], 7), (Q(1),))
        self.assertEqual(isolator_identity([(7, 4)], 7, 3),
                         (Q(4*7**3), Q(4*7**3)))

    def test_orthogonality_and_signs(self):
        entries = [(Q(-4), 1), (Q(3, 2), 5), (Q(5, 3), 2)]
        sp = spectrum(entries)
        for lam, m in sp:
            q = isolating_polynomial(sp, lam)
            self.assertEqual(len(q), len(sp))
            for other, _ in sp:
                self.assertEqual(polynomial_eval(q, other) == 0, other != lam)
            self.assertTrue(isolation_certificate(sp, lam)["nonzero_scale"])

    def test_random_rational_spectra(self):
        rng = random.Random(261100793)
        pool = sorted({Q(a,b) for a in range(-15,16) if a for b in range(1,6)})
        for size in range(1, 9):
            for _ in range(14):
                entries=[(lam,rng.randrange(1,7))
                         for lam in rng.sample(pool,size)]
                for lam,_ in entries:
                    c=isolation_certificate(entries,lam,powers=(1,2,4,7,11))
                    self.assertEqual(len(c["polynomial"]),size)

    def test_repeated_eigenvalues(self):
        entries=[(2,2),(2,3),(3,4)]
        self.assertEqual(spectrum(entries),((Q(2),5),(Q(3),4)))
        self.assertEqual(isolating_polynomial(entries,2),(Q(-3),Q(1)))
        self.assertEqual(isolator_identity(entries,2,5),
                         (Q(-5*2**5), Q(-5*2**5)))

    def test_canceled_and_absent_poles(self):
        with self.assertRaisesRegex(ValueError,"zero aggregated"):
            isolating_polynomial([(7,1),(7,-1),(3,1)],7)
        with self.assertRaisesRegex(ValueError,"zero aggregated"):
            isolating_polynomial([(2,1),(3,1)],11)

    def test_power_growth_witness(self):
        for a,b,K in ((7,3,10),(4,3,1000),(Q(9,5),Q(7,5),100000),
                      (1,Q(1,2),Q(10**8))):
            n=scalar_geometric_counterexample(a,b,K)
            self.assertGreater(Q(a)**n, Q(K)*Q(b)**n)
        with self.assertRaises(ValueError):
            scalar_geometric_counterexample(3,3,100)
        with self.assertRaises(ValueError):
            scalar_geometric_counterexample(2,3,100)

    def test_positive_trace_power_requirement(self):
        with self.assertRaisesRegex(ValueError,"positive"):
            isolator_identity([(3,1)],3,0)

if __name__ == "__main__":
    unittest.main()
