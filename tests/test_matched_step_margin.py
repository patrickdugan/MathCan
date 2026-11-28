"""NRF-09 exact-rational objective and eight-arm median robustness checks."""
import random
import unittest
from fractions import Fraction as Q
from research.compactification.matched_step_margin import (
    margin_decomposition, score, median8, signed_margin, score_drift_bound,
    certified_margin_drift, certified_sign)

class MatchedStepMathTests(unittest.TestCase):
    def test_path_identity_exact(self):
        g=random.Random(9)
        for _ in range(1000):
            a,b,c=(Q(g.randint(-50,50),g.randint(1,10)) for i in range(3))
            x,y,z=margin_decomposition(a,b,c)
            self.assertEqual(x,y+z)

    def test_median_lipschitz_exact(self):
        g=random.Random(907)
        for _ in range(1200):
            x=[Q(g.randint(-80,80),10) for i in range(8)]
            d=Q(g.randint(0,30),10)
            y=[v+Q(g.randint(-10,10),10)*d for v in x]
            delta=max(abs(a-b) for a,b in zip(x,y))
            self.assertLessEqual(abs(median8(y)-median8(x)),delta)
        x=[Q(i,2) for i in range(8)]
        d=Q(5,7)
        self.assertEqual(median8([a+d for a in x])-median8(x),d)

    def test_arm_bound_900_instances(self):
        g=random.Random(190)
        for _ in range(900):
            args=[Q(g.randint(0,80),20) for i in range(4)]
            lam=Q(g.randint(0,50),10)
            self.assertLessEqual(
                abs(score(args[2],args[3],lam)-score(args[0],args[1],lam)),
                score_drift_bound(*args,lam))

    def test_joint_eight_arm_bound(self):
        g=random.Random(104)
        for _ in range(400):
            gen=lambda:(Q(g.randint(0,40),10),Q(g.randint(0,40),10))
            old_sup,new_sup=gen(),gen()
            old_controls=[gen() for _ in range(8)]
            new_controls=[gen() for _ in range(8)]
            lam=Q(g.randint(0,20),10)
            before=signed_margin(old_sup,old_controls,lam)
            after=signed_margin(new_sup,new_controls,lam)
            envelope=certified_margin_drift(
                old_sup,new_sup,old_controls,new_controls,lam)
            self.assertLessEqual(abs(after-before),envelope)
            sign=certified_sign(before,envelope)
            if sign:
                self.assertEqual(sign,1 if after>0 else -1)

    def test_nonnegative_domain_and_controls(self):
        with self.assertRaises(ValueError):median8([Q(1)]*7)
        with self.assertRaises(ValueError):score(0,-1,1)
        with self.assertRaises(ValueError):score(0,1,-1)
        with self.assertRaises(ValueError):certified_sign(1,-1)

if __name__=="__main__":
    unittest.main()
