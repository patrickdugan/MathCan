import importlib.util
from fractions import Fraction
from itertools import product
from pathlib import Path
import unittest

SRC=Path(__file__).resolve().parents[1] / 'research' / 'orbit_lock' / 'weighted_frontier.py'
spec=importlib.util.spec_from_file_location('weighted_frontier',SRC)
wf=importlib.util.module_from_spec(spec)
spec.loader.exec_module(wf)


class WeightedFrontierTests(unittest.TestCase):
    def test_independent_subset_sum_oracle(self):
        for vals in ((1,2,3),(1,3,6),(1,1,2,4),(1,2,4,8)):
            p=tuple(Fraction(v,sum(vals)) for v in vals)
            result=wf.two_code_optimal(p)
            all_scores=[]
            for bits in product((0,1),repeat=len(p)):
                q=sum((v for b,v in zip(bits,p) if b),Fraction(0))
                all_scores.append(1-q*q-(1-q)*(1-q))
            self.assertEqual(result['tv'],max(all_scores))

    def test_onebit_exact_curve_and_nonmonotonicity(self):
        rows=[wf.three_matching_onebit(t) for t in range(9)]
        self.assertEqual(rows[0]['optimal_onebit_tv'],'0')
        self.assertEqual(rows[1]['optimal_onebit_tv'],'1/2')
        self.assertEqual(rows[2]['optimal_onebit_tv'],'15/32')
        self.assertGreater(Fraction(rows[1]['optimal_onebit_tv']),
                           Fraction(rows[2]['optimal_onebit_tv']))
        self.assertEqual(rows[1]['optimal_onebit_balanced_accuracy'],'3/4')
        self.assertTrue(all(Fraction(rows[i+1]['full_relational_tv']) >
                            Fraction(rows[i]['full_relational_tv'])
                            for i in range(len(rows)-1)))

    def test_uniform_and_six_vertex_first_step(self):
        self.assertEqual(wf.two_code_optimal([Fraction(1,15)]*15)['tv'],Fraction(112,225))
        distribution=[Fraction(1,2)]+[Fraction(1,12)]*6+[Fraction(0)]*8
        self.assertEqual(wf.two_code_optimal(distribution)['tv'],Fraction(1,2))

    def test_bad_distribution(self):
        for p in ((Fraction(-1),Fraction(2)),(Fraction(1,3),Fraction(1,3)),()):
            with self.assertRaises(ValueError):
                wf.two_code_optimal(p)

if __name__=='__main__':
    unittest.main()
