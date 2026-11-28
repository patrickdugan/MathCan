import importlib.util
import math
from fractions import Fraction
from pathlib import Path
import unittest

SRC=(Path(__file__).resolve().parents[1] / "research" / "orbit_lock"
     / "transport_identification_bounds.py")
spec=importlib.util.spec_from_file_location("transport_identification_bounds",SRC)
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class TransportIdentificationBoundTests(unittest.TestCase):
    def test_exact_histogram_and_one_observation_elimination(self):
        self.assertEqual(m.check_histogram(m.FULL_HIST,720),Fraction(7,15))
        self.assertEqual(m.check_histogram(m.TRAIN_HIST,576),Fraction(1,2))
        self.assertEqual(1+m.expected_false(m.TRAIN_HIST,576,1),720)

    def test_exact_survival_counts(self):
        self.assertEqual(m.expected_false(m.TRAIN_HIST,576,2),Fraction(572,9))
        self.assertEqual(m.expected_false(m.TRAIN_HIST,576,12),
                         Fraction(207626724431490125202001,70663864180791861451948032))
        self.assertLess(m.expected_false(m.TRAIN_HIST,576,12),Fraction(3,1000))

    def test_noise_bound_specializes_to_clean(self):
        for n in (1,2,3,4,6,8,12):
            got=m.noisy_union_bound(m.TRAIN_HIST,576,n,Fraction(0))
            exp=min(1.0,float(m.expected_false(m.TRAIN_HIST,576,n)))
            self.assertAlmostEqual(got,exp,places=12)

    def test_noisy_chernoff_monotonicity(self):
        for eps in (Fraction(0),Fraction(1,10),Fraction(1,4)):
            b12=m.noisy_union_bound(m.TRAIN_HIST,576,12,eps)
            b24=m.noisy_union_bound(m.TRAIN_HIST,576,24,eps)
            self.assertGreaterEqual(b12,b24)
        self.assertLess(m.noisy_union_bound(m.TRAIN_HIST,576,24,Fraction(1,4)),0.006)

    def test_general_information_count_qualification(self):
        self.assertLess(15**3,720*15)
        self.assertGreaterEqual(15**4,720*15)
        self.assertEqual(m.audit()["first_positive_remaining"],720)

    def test_reject_bad_histogram(self):
        for h in ({576:2},{1:-3,576:1},{-1:10799,576:1}):
            with self.assertRaises(ValueError):
                m.check_histogram(h,576)


if __name__=="__main__":
    unittest.main()
