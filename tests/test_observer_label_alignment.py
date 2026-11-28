"""Exact finite algebra for COE-09, standard library only."""
import itertools
import math
import unittest
from fractions import Fraction


def complete_hits(codes):
    return sum(codes[i]!=codes[j] for i in range(len(codes)) for j in range(i+1,len(codes)))

class Theorems(unittest.TestCase):
    def test_all_three_state_code_permutations(self):
        for codes in itertools.product(range(3),repeat=3):
            for p in itertools.permutations(range(3)):
                self.assertEqual(complete_hits(codes),complete_hits([codes[i] for i in p]))

    def test_derangement_family_separation_and_zero_accuracy(self):
        for n in range(2,21):
            codes=list(range(n));target=[(i+1)%n for i in range(n)]
            self.assertEqual(complete_hits(codes),n*(n-1)//2)
            self.assertEqual(sum(codes[i]==target[i] for i in range(n)),0)

    def test_dark_rotation_exact_rational_pythagorean(self):
        # Rational cos=3/5, sin=4/5, all small rational vectors.
        for a,b in itertools.product(range(-6,7),repeat=2):
            x,y=Fraction(a),Fraction(b)
            rx=(3*x-4*y)/5;ry=(4*x+3*y)/5
            self.assertEqual(rx*rx+ry*ry,x*x+y*y)
            # For a 3D state (visible,x,y), the visible coordinate is fixed.
            for visible in (Fraction(-3,2),Fraction(0),Fraction(9,4)):
                self.assertEqual(visible*visible+rx*rx+ry*ry,
                                 visible*visible+x*x+y*y)

    def test_fixed_decoder_random_true_permutation_exact_mean(self):
        # When predictions remain fixed and test labels are assigned one-to-one
        # uniformly at random, expected #correct = 1, even if predictions tie.
        for n in (2,3,4,5):
            predictions=[(i*i)%n for i in range(n)]
            perms=list(itertools.permutations(range(n)))
            wins=sum(sum(predictions[i]==p[i] for i in range(n)) for p in perms)
            self.assertEqual(Fraction(wins,len(perms)),1)

if __name__=='__main__':unittest.main()
