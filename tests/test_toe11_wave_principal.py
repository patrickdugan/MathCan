"""Exact projected WKB symbol, with an explicit full-theory completeness gate."""
import random
import unittest
from fractions import Fraction as Q

from research.toe.wave_principal import construct_symbol,example,symbol_at,evaluate_polynomial


class ProjectedWaveTests(unittest.TestCase):
    @staticmethod
    def params():
        return dict(electric=(2,Q(1001,1000)), magnetic=(1,0),
                    A=Q(2,5),Bcurv=1,alpha=Q(3,500),
                    beta=Q(1,100),sigma=Q(1,100))

    def setUp(self):
        self.s=construct_symbol(**self.params())

    def test_exact_even_odd_parity(self):
        for omega in (-3,-2,-1,0,1,2,3):
            a=self.s.at(omega);b=self.s.at(-omega)
            self.assertEqual(a[0],b[0])
            self.assertEqual(a[1],-b[1])
            self.assertEqual(a[2],b[2])

    def test_sixth_order_coefficients(self):
        self.assertEqual(len(self.s.determinant),4)
        self.assertNotEqual(self.s.determinant[-1],0)
        self.assertEqual(self.s.det_at(2),evaluate_polynomial(self.s.determinant,4))

    def test_gravitational_mode_double_root(self):
        x=self.s.doubled_gravity_root
        coeffs=self.s.determinant
        self.assertEqual(evaluate_polynomial(coeffs,x),0)
        self.assertEqual(coeffs[1]+2*coeffs[2]*x+3*coeffs[3]*x*x,0)
        self.assertNotEqual(2*coeffs[2]+6*coeffs[3]*x,0)

    def test_double_root_matches_diagonal_induced_operator(self):
        s=self.s
        self.assertEqual(s.doubled_gravity_root,Q(480993997,493000000))

    def test_remaining_mode_real_in_sample(self):
        r=self.s.remaining_root()
        self.assertGreater(r,0)
        self.assertEqual(evaluate_polynomial(self.s.determinant,r),0)
        self.assertNotEqual(r,self.s.doubled_gravity_root)

    def test_mixed_cubic_nonzero(self):
        self.assertTrue(any(self.s.rf))
        self.assertNotEqual(self.s.at(1)[1],0)

    def test_one_metric_mode_one_gauge_tensor_mode(self):
        x=example()
        self.assertTrue(x['all_positive_roots'])
        self.assertIs(x['strong_hyperbolicity_verified'],False)
        self.assertEqual(x['schema'],'mathcan.toe11.projected_wave.v1')

    def test_projected_wave_against_six_dimensional_runtime(self):
        for w in (Q(-5,2),Q(-3,4),Q(0),Q(7,6),Q(7,2)):
            res=symbol_at(w,**self.params())
            self.assertEqual(self.s.at(w),(res['rr'],res['rf'],res['ff']))

    def test_repeated_root_random_rational_backgrounds(self):
        r=random.Random(10411)
        for _ in range(20):
            E=[Q(r.randint(-4,4),10) for j in range(2)]
            B=[Q(r.randint(-4,4),10) for j in range(2)]
            opts=dict(self.params(),electric=E,magnetic=B,
                      alpha=Q(1,60),sigma=Q(1,80))
            p=construct_symbol(**opts)
            x=p.doubled_gravity_root
            self.assertGreater(x,0)
            self.assertEqual(evaluate_polynomial(p.determinant,x),0)
            self.assertEqual(p.determinant[1]+2*p.determinant[2]*x+3*p.determinant[3]*x*x,0)

    def test_projected_polynomial_coupling_not_full_tensor_system(self):
        out=example()
        self.assertTrue('single TT metric' in out['scope'])
        self.assertIs(out['strong_hyperbolicity_verified'],False)

if __name__=='__main__':unittest.main()
