"""DEL-12 exact polynomial derivative tests, including characteristic two."""
from itertools import product
import random
import unittest

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del12_oracle import (
    normalize, conic_polynomial, evaluate, pderiv,
    derivative_conic_certificate, critical_point, discriminant,
    inseparable_frobenius_square, tangent_line_counterexample,
)
from research.deligne_sign_audit.del12_verify_tasks import verify


class Deligne12PolynomialJacobianTests(unittest.TestCase):
    def test_all_80_oracle_cases(self):
        self.assertEqual(sum(verify().values()),80)

    def test_symbolic_polynomial_derivatives_all_fields(self):
        rng=random.Random(261100812)
        for name,f in FIELDS.items():
            for _ in range(75):
                a,b,c,x,y=(rng.randrange(f.q) for _ in range(5))
                r=derivative_conic_certificate(f,a,b,c,x,y)
                self.assertTrue(r["symbolic_dx_ok"],name)
                self.assertTrue(r["symbolic_dy_ok"],name)
                self.assertEqual(r["dx_value"],f.add(y,a))
                self.assertEqual(r["dy_value"],f.add(x,b))

    def test_true_critical_points_iff_discriminant(self):
        rng=random.Random(261100813)
        for name,f in FIELDS.items():
            for _ in range(75):
                a,b,c=(rng.randrange(f.q) for _ in range(3))
                x,y,r=critical_point(f,a,b,c)
                self.assertEqual(r["dx_value"],0)
                self.assertEqual(r["dy_value"],0)
                self.assertEqual(r["value"],discriminant(f,a,b,c))
                self.assertEqual(r["value"]==0,
                                 c==f.mul(a,b))

    def test_all_small_field_conic_solutions_obey_derivative_rule(self):
        for name in ("F2","F3","F4","F5"):
            f=FIELDS[name]
            for a,b,c in product(range(f.q),repeat=3):
                P=conic_polynomial(f,a,b,c)
                px,py=pderiv(f,P,0),pderiv(f,P,1)
                critical_count=0
                for x,y in product(range(f.q),repeat=2):
                    if evaluate(f,P,x,y)!=0:
                        continue
                    both_zero=(evaluate(f,px,x,y)==0 and
                               evaluate(f,py,x,y)==0)
                    if both_zero:
                        critical_count+=1
                        self.assertEqual(c,f.mul(a,b),
                                         (name,a,b,c,x,y))
                self.assertEqual(critical_count,int(c==f.mul(a,b)),
                                 (name,a,b,c))

    def test_inseparable_frobenius_square_in_characteristic_two(self):
        for name in ("F2","F4","F8","F16"):
            f=FIELDS[name]
            for c in (0,1):
                P,dx=inseparable_frobenius_square(f,c)
                self.assertFalse(dx)
                self.assertEqual(evaluate(f,P,c,0),0)

    def test_tangent_line_counterexample(self):
        for name,f in FIELDS.items():
            r=tangent_line_counterexample(f)
            self.assertTrue(all(r.values()),(name,r))

    def test_wrong_swapped_gradient_is_rejected(self):
        for name,f in FIELDS.items():
            a,b,c=1,0,0
            x,y,r=critical_point(f,a,b,c)
            self.assertEqual(r["dx_value"],0)
            self.assertEqual(r["dy_value"],0)
            self.assertNotEqual(f.add(y,b),0)

    def test_pderiv_polynomial_linear_terms(self):
        for name,f in FIELDS.items():
            P=normalize(f,[(3%f.p,(1,0)),(2%f.p,(0,1))])
            dx=pderiv(f,P,0)
            dy=pderiv(f,P,1)
            self.assertEqual(evaluate(f,dx,0,0),3%f.p)
            self.assertEqual(evaluate(f,dy,0,0),2%f.p)

    def test_polynomial_derivative_in_odd_characteristic(self):
        for name in ("F3","F5","F9","F25","F27"):
            f=FIELDS[name]
            P=normalize(f,[(1,(2,0)),(1,(0,0))])
            dx=pderiv(f,P,0)
            for x in range(f.q):
                self.assertEqual(evaluate(f,dx,x,0),
                                 f.mul(2,x))

    def test_reject_nonpolynomial_exponents(self):
        f=FIELDS["F4"]
        with self.assertRaisesRegex(ValueError,"nonnegative"):
            normalize(f,[(1,(-1,0))])
        with self.assertRaisesRegex(ValueError,"two"):
            normalize(f,[(1,(0,0,0))])

    def test_zero_derivative_of_constant(self):
        for name,f in FIELDS.items():
            for c in range(min(f.q,5)):
                P=normalize(f,[(c,(0,0))])
                self.assertFalse(pderiv(f,P,0))
                self.assertFalse(pderiv(f,P,1))

    def test_product_rule_on_conic_x_y(self):
        for name,f in FIELDS.items():
            P=normalize(f,[(1,(1,1))])
            self.assertEqual(pderiv(f,P,0),
                             normalize(f,[(1,(0,1))]))
            self.assertEqual(pderiv(f,P,1),
                             normalize(f,[(1,(1,0))]))


if __name__=="__main__":
    unittest.main()
