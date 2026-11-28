import itertools
import unittest
from fractions import Fraction

class JacobianSecantTests(unittest.TestCase):
    def test_f7_endpoint_remainder_all_2401(self):
        for a,b,x,y in itertools.product(range(7),repeat=4):
            f=lambda t:(a*t*t+b*t)%7
            delta=(y+7-x)%7
            left=(f(y)+7-f(x))%7
            right=((2*a*y+b)*delta+7-(a*delta*delta)%7)%7
            self.assertEqual(left,right)

    def test_quadratic_real_exact_remainder(self):
        for a,b,c,x,y in itertools.product((Fraction(-2),Fraction(0),Fraction(3)),repeat=5):
            F=lambda v:a*v*v+b*v+c
            d=y-x
            error=F(y)-F(x)-(2*a*y+b)*d
            self.assertEqual(error,-a*d*d)

    def test_vector_linear_map_zero_secant_remainder(self):
        # Affine maps have zero Jacobian-Lipschitz constant.
        A=((Fraction(2,5), Fraction(1,10)),(Fraction(0),Fraction(-1,4)))
        x=(Fraction(1),Fraction(2));y=(Fraction(3),Fraction(-1))
        d=tuple(q-p for p,q in zip(x,y))
        for row in A:
            left=sum(z*q for z,q in zip(row,y))-sum(z*q for z,q in zip(row,x))
            self.assertEqual(left,sum(z*q for z,q in zip(row,d)))

if __name__=='__main__':unittest.main()
