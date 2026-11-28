"""OLM-09 exact endpoint causal dominance and robustness regression."""
import sys
from pathlib import Path
import unittest
from fractions import Fraction as Q
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import endpoint_ordering as e


class EndpointOrderingTests(unittest.TestCase):
    def test_strict_finite_ranking(self):
        a=e.squared_effect((e.interval(19,21),),(e.interval(0,0),))
        b=e.squared_effect((e.interval(9,11),),(e.interval(0,0),))
        self.assertEqual(a,(Q(361),Q(441)))
        self.assertEqual(b,(Q(81),Q(121)))
        self.assertEqual(e.ordering(a,b),'active_greater')
        self.assertEqual(e.ordering(b,a),'control_greater')

    def test_nonzero_interval_error_and_ties(self):
        z=e.interval(Q(-1),Q(1))
        self.assertEqual(e.square(z),(Q(0),Q(1)))
        clean=(e.interval(0,0),e.interval(0,0))
        active=(e.interval(Q(19,10),Q(21,10)),e.interval(0,0))
        control=(e.interval(Q(9,10),Q(11,10)),e.interval(0,0))
        a=e.squared_effect(active,clean)
        b=e.squared_effect(control,clean)
        self.assertEqual(e.ordering(a,b),'active_greater')
        self.assertEqual(e.ordering(a,a),'inconclusive')
        self.assertEqual(e.ordering(e.interval(0,1),e.interval(1,2)),'inconclusive')

    def test_strict_robust_lipschitz_margin(self):
        active=e.interval(Q(361,100),Q(441,100))
        control=e.interval(Q(81,100),Q(121,100))
        good=e.robust_ordering(active,control,1,Q(1,5),Q(1,100),Q(1,100),Q(1,100))
        self.assertTrue(good['certified'])
        bad=e.robust_ordering(active,control,200,Q(1,5),Q(1,100),Q(1,100),Q(1,100))
        self.assertFalse(bad['certified'])

    def test_exact_dyadic_root_enclosures(self):
        for n in range(10):
            x=Q(n,7)
            lo=e.sqrt_lower(x,24)
            hi=e.sqrt_upper(x,24)
            self.assertLessEqual(lo*lo,x)
            self.assertGreaterEqual(hi*hi,x)
            self.assertLessEqual(hi-lo,Q(1,2**24))

    def test_invalid_shapes_and_interval_rejection(self):
        with self.assertRaises(ValueError):e.interval(2,1)
        with self.assertRaises(ValueError):e.squared_effect((),())
        with self.assertRaises(ValueError):e.squared_effect((e.interval(0,1),),())
        with self.assertRaises(ValueError):e.robust_ordering(
            e.interval(0,1),e.interval(0,1),1,1,-1,0,0)


if __name__=="__main__":
    unittest.main()
