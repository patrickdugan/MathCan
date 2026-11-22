"""DEL-03: exact spectral/Hankel identities and cancellation mutants."""
import random
import unittest
from fractions import Fraction as Q
from research.deligne_sign_audit.power_sum_poles import (
    spectrum,power_trace,hankel,determinant,vandermonde_det_squared,
    polynomial_from_roots,recover_monic_recurrence,pole_coefficient,certificate)

class SpectralPoleTests(unittest.TestCase):
 def test_random_rational_multisets(self):
    rng=random.Random(261100792)
    pool=sorted({Q(a,b) for a in range(-15,16) if a for b in range(1,6)})
    for size in range(1,8):
        for _ in range(14):
            entries=[(v,rng.randrange(1,6)) for v in rng.sample(pool,size)]
            self.assertEqual(certificate(entries)["distinct_eigenvalues"],size)
 def test_repeated_eigenvalues_aggregate(self):
    entries=[(Q(2,3),2),(Q(2,3),5),(-4,1),(-4,3)]
    self.assertEqual(spectrum(entries),((Q(-4),4),(Q(2,3),7)))
    self.assertEqual(pole_coefficient(entries,Q(2,3)),7)
    self.assertEqual(pole_coefficient(entries,-4),4)
    self.assertEqual(determinant(hankel(entries)),
                     vandermonde_det_squared(entries))
    self.assertEqual(recover_monic_recurrence(entries),
                     polynomial_from_roots(entries))
 def test_opposite_eigenvalues_hide_in_first_power(self):
    entries=[(7,1),(-7,1)]
    self.assertEqual(power_trace(entries,1),0)
    self.assertEqual(power_trace(entries,2),98)
    self.assertEqual(power_trace(entries,3),0)
    self.assertEqual(power_trace(entries,4),4802)
    self.assertEqual(determinant(hankel(entries)),-9604)
    self.assertEqual(recover_monic_recurrence(entries),
                     (Q(-49),Q(0),Q(1)))
 def test_virtual_cancellation(self):
    entries=[(7,1),(7,-1),(3,1)]
    self.assertEqual(spectrum(entries,True),((Q(3),1),))
    self.assertEqual(pole_coefficient(entries,7,True),0)
    self.assertEqual(pole_coefficient(entries,3,True),1)
    self.assertEqual(power_trace(entries,8,True),3**8)
    with self.assertRaisesRegex(ValueError,"positive"):
        spectrum(entries)
    self.assertEqual(determinant(hankel(entries,size=2,allow_virtual=True)),0)
 def test_zero_eigenvalue_rejected(self):
    with self.assertRaisesRegex(ValueError,"nonzero"):
        spectrum([(0,1)])
 def test_short_trace_window_fails(self):
    entries=[(7,1),(-7,1)]
    self.assertEqual(power_trace(entries,1),0)
    self.assertGreater(power_trace(entries,2),1)
    self.assertGreater(power_trace(entries,10),10**8)
 def test_distinct_pole_recovery(self):
    entries=[(-4,1),(Q(1,5),7),(Q(3,2),2),(5,3)]
    c=certificate(entries)
    self.assertEqual(c["distinct_eigenvalues"],4)
    self.assertEqual(len(c["monic_coefficients"]),5)
    for lam,m in spectrum(entries):
        self.assertEqual(pole_coefficient(entries,lam),m)

if __name__=="__main__":
    unittest.main()
