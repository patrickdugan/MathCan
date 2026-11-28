"""COE-08: independent exact-combinatorial arithmetic reference for MathCan."""
from fractions import Fraction
from itertools import permutations
from math import comb
import unittest

LABEL=[10,8,2,5,8,7,6,10,8]
H8COUNT=[12,2,3,1,1,8,2,8,27]
H8BRAC=[12,2,2,1,1,1,5,1,1,1,1,1,8,27]
H16COUNT=[11,1,1,1,2,1,1,2,2,1,6,2,7,26]
H16BRAC=[11,1,1,1,1,2,1,1,1,1,1,5,1,1,1,1,7,26]

def falling(n,k):
    x=1
    for t in range(k):x*=max(0,n-t)
    return x

def exact_second_moment(class_hist, label_hist, edges, adjacent):
    N=sum(label_hist)
    e=edges
    p=1-Fraction(sum(falling(m,2) for m in label_hist),falling(N,2))
    pa=Fraction(sum(m*falling(N-m,2) for m in label_hist),falling(N,3))
    both_same=sum(falling(m,4) for m in label_hist)+sum(
        falling(m,2)*falling(n,2) for i,m in enumerate(label_hist)
        for j,n in enumerate(label_hist) if i!=j)
    pd=1-2*(1-p)+Fraction(both_same,falling(N,4))
    disjoint=comb(e,2)-adjacent
    mean=e*p
    variance=e*p+2*adjacent*pa+2*disjoint*pd-mean*mean
    return mean,variance

class ObserverNullArithmetic(unittest.TestCase):
    def test_histograms_and_distinct_labels(self):
        self.assertEqual(sum(LABEL),64)
        self.assertEqual(comb(64,2)-sum(comb(x,2) for x in LABEL),1795)
        self.assertEqual(sum(x*x for x in H8COUNT),1020)
        self.assertEqual(sum(x*x for x in H8BRAC),978)
        self.assertEqual(sum(x*x for x in H16COUNT),904)
        self.assertEqual(sum(x*x for x in H16BRAC),888)

    def test_shuffled_mean_in_closed_form(self):
        E=1795;N=64
        for c,b,expect in [(H8COUNT,H8BRAC,Fraction(1795,96)),
                           (H16COUNT,H16BRAC,Fraction(1795,252))]:
            self.assertEqual(Fraction(E*(sum(x*x for x in c)-sum(x*x for x in b)),N*(N-1)),expect)

    def test_shuffled_second_moments(self):
        self.assertEqual(exact_second_moment(H8COUNT,LABEL,21,79),
                         (Fraction(1795,96),Fraction(11285015,5809152)))
        self.assertEqual(exact_second_moment(H16COUNT,LABEL,8,10),
                         (Fraction(1795,252),Fraction(46069057,60043032)))

    def test_no_label_interpretation_from_pair_differences(self):
        # A label-blind bit process can separate almost every pair just by noise.
        p=Fraction(1,9)
        P_diff=1-(p*p+(1-p)*(1-p))**8
        self.assertGreater(P_diff,Fraction(4,5))
        self.assertLess(P_diff,Fraction(5,6))

if __name__=='__main__':unittest.main()
