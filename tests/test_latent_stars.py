import importlib.util
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import unittest

SRC = Path(__file__).resolve().parents[1] / 'research' / 'orbit_lock' / 'latent_stars.py'
spec=importlib.util.spec_from_file_location('latent_stars',SRC)
ls=importlib.util.module_from_spec(spec)
spec.loader.exec_module(ls)


class LatentStarsTests(unittest.TestCase):
    def test_all_455_three_holdout_patterns(self):
        r=ls.enumerate_partial_rigidity()
        self.assertEqual(r['unique_global_star_covers'],455)
        self.assertEqual(r['direct_six_clique_cases'],80)
        self.assertEqual(r['extra_clique_cases_resolved_by_global_cover'],375)
        self.assertEqual([a['count'] for a in r['classes']],[80,180,180,15])
        self.assertEqual([a['star_candidate_cliques'] for a in r['classes']],[6,13,24,47])

    def test_all_1365_four_holdout_identifiability_boundary(self):
        result=ls.enumerate_four_missing_boundary()
        self.assertEqual(result['unique_reconstructions'],1320)
        self.assertEqual(result['exactly_two_reconstructions'],45)
        self.assertTrue(result['ambiguous_iff_two_disjoint_pairs_of_omitted_matchings_share_an_edge'])

    def test_covariance_types_against_independent_matching_enumeration(self):
        for k in (2,3,4):
            ms=tuple(ls.matchings(range(2*k)))
            e=(0,1)
            p=Fraction(sum(e in m for m in ms),len(ms))
            for f in ((0,2),(2,3)):
                joint=Fraction(sum(e in m and f in m for m in ms),len(ms))
                direct=joint-p*p
                name='covariance_incident' if set(e)&set(f) else 'covariance_disjoint'
                self.assertEqual(direct,ls.covariance_types(k)[name])
                self.assertEqual(ls.covariance_types(k,Fraction(9,10),Fraction(1,10))[name],
                                 Fraction(16,25)*direct)

    def test_exact_repetition_probabilities_and_union_error(self):
        a=ls.repeated_mask_probability(16)
        b=ls.repeated_mask_probability(40,Fraction(3,4),Fraction(1,4))
        c=ls.repeated_mask_probability(64,Fraction(3,4),Fraction(1,4))
        self.assertGreater(a['exact_success_float'],0.996)
        self.assertGreater(b['exact_success_float'],0.955)
        self.assertGreater(c['exact_success_float'],0.998)
        self.assertGreater(c['exact_success_float'],b['exact_success_float'])
        for e in (a,b,c):
            self.assertGreaterEqual(e['union_error_float'],1-e['exact_success_float'])

    def test_invalid_input(self):
        for args in ((0,Fraction(3,4),Fraction(1,4)),
                     (4,Fraction(1,4),Fraction(3,4)),
                     (3,Fraction(1,2),Fraction(1,4))):
            with self.assertRaises(ValueError):
                ls.repeated_mask_probability(*args)
        with self.assertRaises(ValueError):
            ls.covariance_types(1)

if __name__ == '__main__':
    unittest.main()
