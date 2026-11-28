import importlib.util
from fractions import Fraction
from itertools import product
from pathlib import Path
import unittest

SRC=Path(__file__).resolve().parents[1] / 'research' / 'orbit_lock' / 'finite_memory.py'
spec=importlib.util.spec_from_file_location('finite_memory',SRC)
fm=importlib.util.module_from_spec(spec)
spec.loader.exec_module(fm)

class MemoryFrontierTests(unittest.TestCase):
    def test_exhaustive_balanced_partition_optimal(self):
        for m in (3,4,5):
            for r in range(1,min(m,4)+1):
                self.assertEqual(fm.exhaustive_frontier(m,r)[0],fm.frontier(m,r)['tv'])

    def test_stochastic_channels_dominated_by_deterministic(self):
        for probs in product((Fraction(0),Fraction(1,2),Fraction(1)),repeat=4):
            cert=fm.channel_certificate([{0:p,1:1-p} for p in probs])
            self.assertLessEqual(cert['tv'],fm.frontier(4,2)['tv'])
            self.assertLessEqual(cert['best_recovery'],Fraction(1,2))

    def test_exact_recovery_and_bit_frontier(self):
        expected={1:Fraction(0),2:Fraction(112,225),3:Fraction(2,3),
                  4:Fraction(56,75),5:Fraction(4,5),15:Fraction(14,15)}
        for r,score in expected.items():
            cert=fm.frontier(15,r)
            self.assertEqual(cert['tv'],score)
            self.assertEqual(cert['recovery'],Fraction(r,15))
            self.assertEqual(cert['balanced_accuracy'],(1+score)/2)

    def test_permutation_stabilizer_count(self):
        for k in range(2,7):
            result=fm.stabilizer_quotient(k)
            matchings=1
            for j in range(1,k+1):
                matchings*=2*j-1
            self.assertEqual(result['matching_states'],matchings)
            self.assertLess(result['minimum_exact_bits'],result['full_group_bits'])

    def test_circle_code_and_quantized_separation(self):
        for m in (3,15,105):
            witnesses=[fm.circle_probe(m,b) for b in range(18)]
            self.assertTrue(any(q['sufficient_analytic_bound'] for q in witnesses))
            for w in witnesses:
                if w['sufficient_analytic_bound']:
                    self.assertTrue(w['empirical_separated'])

if __name__=='__main__':
    unittest.main()
