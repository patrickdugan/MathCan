"""Independent small exact/numerical consequences of SPC-03 theorems."""
import itertools
import math
import unittest
from fractions import Fraction

class ContractionAliasingTests(unittest.TestCase):
    def test_exact_dc_energy_identity_on_integer_data(self):
        for z in itertools.product(range(-2,3),repeat=4):
            if sum(z)!=0:continue
            v=sum(i*i for i in z)
            for anchor in (-15,0,23):
                a=[i+anchor for i in z]
                self.assertEqual(sum(i*i for i in a),v+4*anchor*anchor)

    def test_affine_differences_cancel_static_anchor(self):
        for a in range(-4,5):
            for b in range(-3,4):
                for x,y in ((0,1),(5,-7),(2,2)):
                    self.assertEqual((a*x+b)-(a*y+b),a*(x-y))

    def test_decimal_free_contraction_rounding_bound(self):
        # Perturb a geometric recurrence with deterministic alternating noise.
        k=Fraction(2,5)
        eps=Fraction(1,1000)
        exact=Fraction(0); perturbed=exact
        for t in range(1,21):
            exact=k*exact+1
            perturbed=k*perturbed+1+((-1)**t)*eps
            self.assertLessEqual(abs(exact-perturbed),eps*(1-k**t)/(1-k))

    def test_damping_delay_exact_algebra(self):
        # Modulus powers check the common rho^L factor before complex phases.
        rho=Fraction(2,5)
        for delay in range(8):
            for s in (0,1,3,6):
                self.assertEqual(rho**(delay+s),rho**delay*rho**s)

    def test_hankel_rank_of_geometric_sequence(self):
        # For exact rational poles 1/2, 1/3 the rank-two minor is nonzero.
        lam,mu=Fraction(1,2),Fraction(1,3)
        a,b=Fraction(2),Fraction(5)
        def d(t):return a*(lam-1)*lam**t+b*(mu-1)*mu**t
        self.assertNotEqual(d(0)*d(2)-d(1)**2,0)

    def test_affine11_bijection(self):
        self.assertEqual(len({(4*x+7)%11 for x in range(11)}),11)

if __name__=='__main__':unittest.main()
