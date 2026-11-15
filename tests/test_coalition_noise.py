"""Standalone exact integer cross-checks of Lean PEF-06 finite examples."""
import unittest


def latch(m, word):
    return sum(((word>>(2*j))&3)==3 for j in range(m))%2


class CoalitionNoiseOracle(unittest.TestCase):
    def test_singleton_and_three_disjoint_coalition_witnesses(self):
        self.assertEqual(latch(3,0),0)
        self.assertTrue(all(latch(3,1<<i)==0 for i in range(6)))
        self.assertEqual([latch(3,3<<(2*i)) for i in range(3)],[1,1,1])
        for x in range(64):
            if latch(3,x):
                self.assertTrue(any(((x>>(2*j))&3)==3 for j in range(3)))

    def test_weighted_finite_oracles(self):
        for m,target in ((2,30),(3,676)):
            n=2*m
            weighted=sum(3**(n-x.bit_count())
                         for x in range(1<<n) if latch(m,x))
            self.assertEqual(weighted,target)
        discrepancy=sum(3**(4-z.bit_count())
                       for x in range(16) for z in range(16)
                       if latch(2,x)!=latch(2,x^z))
        self.assertEqual(discrepancy,1400)

    def test_average_sensitivity_and_mobius_point(self):
        impact=sum(latch(3,x)!=latch(3,x^(1<<i))
                   for x in range(64) for i in range(6))
        self.assertEqual(impact,192)
        self.assertEqual(3*4**4-6*4**2+4,676)


if __name__=="__main__":
    unittest.main()
