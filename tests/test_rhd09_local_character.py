"""Independent exact finite-ring checks for the RHD-09 character."""
import tempfile
import unittest
from itertools import product
from pathlib import Path
from research.rh_proof_distillation.rhd09_local_character import (
    P, P2, COEFFS, PHI20, dirichlet_exponent, lifted_factors,
    norm, principal_norm, poly_product, theta, training_records, write_data,
)

class LocalCharacterTests(unittest.TestCase):
    def test_factorization_and_irreducible_residues(self):
        fs = lifted_factors()
        self.assertEqual(len(fs), 4)
        self.assertTrue(all((x-y) % P2 == 0 for x,y in zip(poly_product(fs), PHI20)))
        for f, c in zip(fs, COEFFS):
            self.assertEqual(f[0] % P, P-1)
            self.assertEqual(f[1] % P, c % P)
            self.assertEqual(pow((c*c + 4)%P, 14, P), P-1)

    def test_exhaustive_trace_norm_identity(self):
        for f in lifted_factors():
            for a,b in product(range(P),repeat=2):
                n = principal_norm(f,a,b)
                self.assertEqual(n % P, 1)
                self.assertEqual(dirichlet_exponent(n), theta(f,a,b))

    def test_witness_and_kernel(self):
        for f in lifted_factors():
            self.assertEqual(principal_norm(f,15,0),30)
            self.assertEqual(theta(f,15,0),1)
            self.assertEqual(sum(theta(f,a,b)==0 for a,b in product(range(P),repeat=2)), P)
            self.assertEqual(theta(f,0,1), (-f[1])%P)

    def test_character_homomorphism_and_global_units(self):
        units = [x for x in range(P2) if x%P]
        self.assertEqual(dirichlet_exponent(1),0)
        self.assertEqual(dirichlet_exponent(-1),0)
        self.assertEqual(dirichlet_exponent(1+P),1)
        for x in units:
            self.assertEqual(dirichlet_exponent(x*(1+P)),(dirichlet_exponent(x)+1)%P)
        for x in units[::19]:
            for y in units[::17]:
                self.assertEqual(dirichlet_exponent(x*y), (dirichlet_exponent(x)+dirichlet_exponent(y))%P)
        with self.assertRaises(ValueError):
            dirichlet_exponent(29)

    def test_mutation_controls(self):
        f = lifted_factors()[0]
        self.assertNotEqual(norm(f,1+P,0),1+P)
        self.assertNotEqual(theta(f,0,1),1)
        self.assertEqual(theta(f,1,1),(2-f[1])%P)

    def test_corpus_manifest_replay(self):
        rows = list(training_records())
        self.assertEqual(len(rows),4*P*P)
        self.assertEqual({r['split'] for r in rows}, {'train','val','test'})
        self.assertTrue(all(not r['lean_witness_proved'] for r in rows))
        with tempfile.TemporaryDirectory() as folder:
            target = Path(folder)/'data.jsonl'
            a = write_data(target)
            self.assertEqual(a,write_data(target))
            self.assertEqual(a['examples'],len(rows))
            self.assertEqual(sum(a['counts'].values()),len(rows))

if __name__ == '__main__':
    unittest.main()
