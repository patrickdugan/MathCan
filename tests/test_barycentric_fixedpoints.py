"""NRF-02D rational Perron, stochastic-row and soft policy tests."""
import unittest
from fractions import Fraction as Q
from itertools import product
from research.compactification.barycentric_fixedpoints import (
    MixingEdge,incoming_comparison,exact_positive_resolvent,
    smooth_mixture_bound,two_by_two_subcritical_criterion,
)

class BarycentricFixedPointTests(unittest.TestCase):
    def test_subcritical_perron_2x2_grid(self):
        vals=(Q(0),Q(1,4),Q(1,2),Q(1),Q(3,2))
        cases=0
        for a,b,c,d in product(vals,repeat=4):
            m=((a,b),(c,d))
            truth=two_by_two_subcritical_criterion(a,b,c,d)
            if truth:
                w,alpha=exact_positive_resolvent(m)
                self.assertTrue(all(sum((r*x for r,x in zip(row,w)),Q(0))<=alpha*weight
                                    for row,weight in zip(m,w)))
                self.assertLess(alpha,1)
            else:
                with self.assertRaises(ValueError): exact_positive_resolvent(m)
            cases+=1
        self.assertEqual(cases,625)

    def test_averaging_stabilizes_expanding_self_loop(self):
        edges=(MixingEdge("gain","x","x",Q(3,2),Q(1,4)),
               MixingEdge("repair","x","x",Q(1,4),Q(3,4)))
        m=incoming_comparison(("x",),edges)
        self.assertEqual(m,((Q(9,16),),))
        weights,alpha=exact_positive_resolvent(m)
        self.assertEqual(weights,(Q(16,7),))
        self.assertEqual(alpha,Q(9,16))
        self.assertGreater(edges[0].rate,1)

    def test_imbalanced_two_vertex_matrix(self):
        m=((Q(0),Q(2)),(Q(1,4),Q(0)))
        weights,alpha=exact_positive_resolvent(m)
        self.assertEqual(weights,(Q(6),Q(5,2)))
        self.assertEqual(alpha,Q(5,6))
        self.assertGreater(sum(m[0]),1)

    def test_soft_policy_certificate(self):
        rate=smooth_mixture_bound(Q(3,2),Q(1,4),Q(5,16),Q(1,8),Q(3))
        self.assertEqual(rate,Q(53,64))
        self.assertLess(rate,1)

    def test_invalid_stochastic_row(self):
        with self.assertRaises(ValueError):
            incoming_comparison(("x",),(MixingEdge("bad","x","x",Q(1),Q(1,2)),))
        with self.assertRaises(ValueError): exact_positive_resolvent(((Q(3,2),),))
        with self.assertRaises(ValueError): exact_positive_resolvent(((Q(1),),))

if __name__=="__main__":
    unittest.main()
