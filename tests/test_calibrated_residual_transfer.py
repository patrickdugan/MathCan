"""Ten exact Fraction regressions for OLM-21."""
import sys,unittest
from pathlib import Path
from fractions import Fraction as F
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import calibrated_residual_transfer as m
class Tests(unittest.TestCase):
    def test_exact_shrunk_slope(self):self.assertEqual(m.ridge([1,2],[2,4]),F(40,21))
    def test_clip_upper(self):self.assertEqual(m.ridge([1],[10]),2)
    def test_clip_lower(self):self.assertEqual(m.ridge([1],[-10]),-2)
    def test_heavy_tailed_same_distribution_can_worsen_MAE(self):
        o=m.heavy_tail_witness()
        self.assertEqual(o['beta'],F(20,21))
        self.assertEqual(o['direct_MAE'],1)
        self.assertEqual(o['calibrated_MAE'],F(37,21))
    def test_ridge_can_improve_MSE_as_MAE_worsens(self):
        o=m.heavy_tail_witness()
        self.assertLess(o['calibrated_MSE'],o['direct_MSE'])
        self.assertGreater(o['calibrated_MAE'],o['direct_MAE'])
    def test_equal_source_marginal_reverse_transfer(self):
        o=m.flip_witness()
        self.assertTrue(o['source_marginal_constant'])
        self.assertEqual(o['beta'],F(20,21))
        self.assertEqual(o['calibrated_test_MAE'],F(41,21))
        self.assertEqual(o['direct_test_MAE'],1)
    def test_exact_moment_risk_shift(self):
        a=([1,2],[0,3]);b=([1,2],[1,-1])
        for c in (-2,F(1,2),0,4):
            diff,bound=m.risk_shift(a,b,c)
            self.assertEqual(diff,m.risk(*b,c)-m.risk(*a,c))
            self.assertLessEqual(abs(diff),bound)
    def test_sharp_moment_bound(self):
        difference,bound=m.risk_shift(([1],[1]),([1],[2]),0)
        self.assertEqual(abs(difference),bound)
    def test_ridge_first_order_minimizer(self):
        x=[1,-1,2,-2];y=[2*v for v in x];b=m.ridge(x,y)
        xx=sum(v*v for v in x);xy=sum(a*c for a,c in zip(x,y))
        self.assertEqual(F(21,20)*xx*b,xy)
    def test_invalid_data_guard(self):
        for fn,args in [(m.ridge,([0],[1])),(m.ridge,([],[])),
                        (m.risk,([1],[1,2],0)),(m.moments,([1],[1,2]))]:
            with self.assertRaises(ValueError):fn(*args)
if __name__=='__main__':unittest.main()
