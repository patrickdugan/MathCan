"""Exact rational checks for observable-fiber defect transport."""
from fractions import Fraction as Q
import unittest

def F(x):
    a,b=x
    return (a/2+b/4,b/2)

def budget(alpha:Q,delta:Q,steps:int,initial:Q=Q(0))->Q:
    result=initial
    for _ in range(steps):
        result=alpha*result+2*delta
    return result

class ObservableFiberTests(unittest.TestCase):
    def test_sharp_one_step_fiber_defect(self):
        a=F((Q(0),Q(1)))[0]
        b=F((Q(0),Q(-1)))[0]
        self.assertEqual(abs(a-b),Q(1,2))
        self.assertEqual(budget(Q(1,2),Q(1,4),1),Q(1,2))

    def test_repeated_fiber_error_bound(self):
        for a in (-1,0,1):
            for b in (-1,0,1):
                for c in (-1,0,1):
                    for d in (-1,0,1):
                        x=(Q(a),Q(b));y=(Q(c),Q(d))
                        initial=abs(x[0]-y[0])
                        for step in range(1,12):
                            x=F(x);y=F(y)
                            self.assertLessEqual(abs(x[0]-y[0]),
                                budget(Q(1,2),Q(1,4),step,initial))
                            self.assertTrue(all(-1<=v<=1 for v in (*x,*y)))

    def test_exact_quotient_when_dark_coupling_zero(self):
        def g(x):return (x[0]/2,x[1]/2)
        for obs in (-1,0,1):
            self.assertEqual(g((Q(obs),Q(1)))[0],
                             g((Q(obs),Q(-1)))[0])

if __name__ == "__main__":unittest.main()
