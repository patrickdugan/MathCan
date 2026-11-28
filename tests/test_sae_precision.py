import unittest
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'research' / 'orbit_lock'))
from fractions import Fraction
from itertools import combinations
import importlib.util
from pathlib import Path
SRC=Path(__file__).resolve().parents[1] / 'research' / 'orbit_lock' / 'sae_precision.py'
if not SRC.exists(): SRC=Path(__file__).with_name('sae_precision.py')
spec=importlib.util.spec_from_file_location('sae_precision',SRC)
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
topk_stability=mod.topk_stability
matching_stability=mod.matching_stability
silent_atom_witness=mod.silent_atom_witness

class SAEPrecisionTests(unittest.TestCase):
    def test_topk_margin_under_all_bounded_sign_perturbations(self):
        row=(Fraction(7),Fraction(6),Fraction(5),Fraction(2),Fraction(1))
        cert=topk_stability([row],3)
        self.assertEqual(cert['certified_linf_radius'],Fraction(3,2))
        for signs in ((1,-1,1,-1,1),(-1,1,-1,1,-1),(1,1,1,-1,-1)):
            moved=[u+sgn for u,sgn in zip(row,signs)]
            self.assertEqual(set(sorted(range(5),key=lambda j:-moved[j])[:3]),{0,1,2})

    def test_matching_margin_is_sufficient(self):
        matches=((0,1,2),(0,3,4),(1,3,5),(2,4,5))
        scores=(Fraction(10),Fraction(9),Fraction(8),Fraction(1),Fraction(2),Fraction(2))
        r=matching_stability(scores,matches)
        self.assertEqual(r['winning_support'],(0,1,2))
        delta=r['certified_linf_radius']/2
        for signs in ((1,-1,1,-1,1,-1),(-1,1,-1,1,-1,1)):
            changed=[v+sgn*delta for v,sgn in zip(scores,signs)]
            self.assertEqual(matching_stability(changed,matches)['winning_support'],(0,1,2))

    def test_silent_atom_indistinguishability_is_exact(self):
        rows=((0,1,0,1),(1,0,0,1),(0,0,0,1))
        cert=silent_atom_witness(rows,2)
        self.assertTrue(cert['distinct_parameter_vectors'])
        self.assertTrue(cert['identical_training_observations'])
        with self.assertRaises(ValueError):silent_atom_witness(rows,3)

    def test_invalid_score_shape(self):
        with self.assertRaises(ValueError):topk_stability([(1,2),(1,2,3)],1)
        with self.assertRaises(ValueError):matching_stability((1,2,3),((0,1),))

if __name__=='__main__':unittest.main()
