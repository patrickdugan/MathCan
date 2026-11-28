import importlib.util
from fractions import Fraction
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'research' / 'orbit_lock' / 'collision_spectrum.py'
spec = importlib.util.spec_from_file_location('collision_spectrum', SRC)
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


class CollisionSpectrumTests(unittest.TestCase):
    def test_arbitrary_nonneutral_law_and_noise(self):
        q = {s:Fraction(j,21) for s,j in enumerate((1,2,3,4,5,6))}
        f = {s:x for s,x in enumerate((0,1,0,2,1,2))}
        for eps in (Fraction(0),Fraction(1,5),Fraction(1,2),oracle.ONE):
            r=oracle.exact_certificate(q,f,eps)
            self.assertEqual(r['n_observations'],3)
            self.assertEqual(Fraction(r['tv']), (1-eps)*(1-Fraction(r['collision'])))
            self.assertEqual(Fraction(r['centered_cca_singular_value']),1-eps)
            self.assertTrue(r['weighted_gram_verified'])

    def test_orbit_exact_spectra_four_six_vertices(self):
        for k in (2,3):
            for eps in (Fraction(0),Fraction(1,4), Fraction(1,2), oracle.ONE):
                r=oracle.orbit_spectrum(k,eps)
                m=r['n_observations']
                self.assertEqual(r['centered_cca_multiplicity'], m-1)
                self.assertEqual(Fraction(r['collision']),Fraction(1,m))

    def test_zero_noise_perfect_canonical_correlation(self):
        r=oracle.orbit_spectrum(3)
        self.assertEqual(r['centered_cca_singular_value'],'1')
        self.assertEqual(r['centered_cca_multiplicity'],14)
        self.assertEqual(r['tv'],'14/15')

    def test_invalid_laws(self):
        for q,f,eps in (({1:Fraction(2)},{1:1},Fraction(0)),
                        ({1:Fraction(1)},{2:1},Fraction(0)),
                        ({1:Fraction(1)},{1:1},Fraction(-1))):
            with self.assertRaises(ValueError):
                oracle.exact_certificate(q,f,eps)


if __name__=='__main__':
    unittest.main()
