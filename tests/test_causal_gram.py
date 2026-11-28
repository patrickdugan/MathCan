"""OLM-07 exact causal Gram and finite intervention regression tests."""
import sys
import unittest
from fractions import Fraction
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import causal_gram as g


class CausalGramTests(unittest.TestCase):
    def test_gauge_shift_and_permutation_invariance(self):
        result=g.witness()
        self.assertTrue(result['signed_permutation_gram_congruence'])
        self.assertEqual(result['psd_nonnegative_samples'],625)
        self.assertEqual(len(result['causal_gram']),4)

    def test_exact_matrix_product_and_causal_energy(self):
        J=(((g.ONE,g.ZERO),),)
        D=((g.ONE,g.ZERO),(g.ZERO,g.ONE))
        C=g.causal_gram(J,(g.ONE,),D)
        self.assertEqual(C,((g.ONE,g.ZERO),(g.ZERO,g.ZERO)))
        self.assertEqual(g.energy(C,(g.ZERO,Fraction(99))),g.ZERO)
        self.assertEqual(g.energy(C,(Fraction(1,3),g.ZERO)),Fraction(1,9))

    def test_second_order_null_direction_and_sharp_bound(self):
        for r in (Fraction(1,2),Fraction(1,8),Fraction(1,32)):
            result=g.finite_radius_witness(r)
            self.assertTrue(result['quadratic_remainder_bound_sharp'])
            self.assertEqual(Fraction(result['linear_gauge_direction_finite_effect']),r*r)
            self.assertEqual(result['finite_difference_gram'][0][0],'1')
            self.assertEqual(result['finite_difference_gram'][1][1],str(r*r))

    def test_reconstruction_ranking_reversal(self):
        output=g.contrasting_errors(Fraction(100),Fraction(1,10))
        self.assertEqual(output['output_squared_error_of_large_error'],'0')
        self.assertEqual(output['output_squared_error_of_small_error'],'1/100')
        self.assertEqual(output['hidden_norm_squared_large_error'],'10000')

    def test_invalid_inputs_fail_closed(self):
        with self.assertRaises(ValueError):
            g.causal_gram((),(),((1,),(0,)))
        with self.assertRaises(ValueError):
            g.causal_gram(((((g.ONE,g.ZERO),)),),(Fraction(2),),((1,),(1,)))
        with self.assertRaises(ValueError):
            g.finite_radius_witness(Fraction(0))
        with self.assertRaises(ValueError):
            g.contrasting_errors(Fraction(1),Fraction(2))

if __name__=='__main__':
    unittest.main()
