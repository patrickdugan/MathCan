"""RHD-07 exact arithmetic controls and mutation tests."""
from pathlib import Path
import tempfile
import unittest
from research.rh_proof_distillation.rhd07_fieldok_fixture import (
    PIN, SOURCE, blob_sha, classify, factors_mod_prime, generate, is_prime, legendre,
    poly_mul,
)


class FieldOKTests(unittest.TestCase):
    def test_prime_splitting_and_poly_product(self):
        for p in range(5, 1500):
            if not is_prime(p):
                continue
            factors = factors_mod_prime(p)
            self.assertEqual(len(factors), 4 if p % 12 == 1 else 2)
            product = (1,)
            for factor in factors:
                product = poly_mul(product, factor, p)
                if len(factor) == 3:
                    self.assertEqual(legendre(factor[1]**2 - 4*factor[0], p), -1)
            self.assertEqual(product, (1, 0, p-1, 0, 1))

    def test_representatives_for_all_four_classes(self):
        for p, good_d in ((5, (1,)), (7, (3,)), (11, ()), (13, (1, 3))):
            for d in (1, 3):
                row = classify(p, d)
                self.assertEqual(row["fieldok_arithmetic"], d in good_d)
                self.assertEqual(row["joint_arithmetic_gate"], p == 13)
                self.assertFalse(row["full_upstream_Lean_witness_constructed"])

    def test_prime_13_concrete_oneK_pair(self):
        row = classify(13, 1)
        self.assertIn([2, 6], row["oneK_and_apart_residue_pairs"])
        self.assertEqual(pow(2, 3, 13), 8)
        self.assertEqual(pow(6, 3, 13), 8)
        self.assertEqual((2 + pow(2, -1, 13)) % 13, 9)
        self.assertEqual((6 + pow(6, -1, 13)) % 13, 4)

    def test_prime_witness_cardinalities(self):
        rows = generate()
        self.assertEqual(len(rows), 474)
        self.assertEqual(sum(x["fieldok_arithmetic"] for x in rows), 231)
        self.assertEqual(sum(x["joint_arithmetic_gate"] for x in rows), 108)
        self.assertEqual(sum(x["fieldok_arithmetic"] and not x["joint_arithmetic_gate"] for x in rows), 123)

    def test_subfield_action_for_d3(self):
        for p in (13, 37, 61, 73, 97):
            row = classify(p, 3)
            self.assertEqual(len(row["oneK_and_apart_residue_pairs"]), 2)
            for r, s in row["oneK_and_apart_residue_pairs"]:
                self.assertEqual(pow(r, 7, p), s)
                self.assertEqual((2*r*r - 1) % p, (2*s*s - 1) % p)

    def test_mutated_factor_fails_product(self):
        p = 13
        factors = list(factors_mod_prime(p))
        f = list(factors[0])
        f[0] = (f[0] + 1) % p
        factors[0] = tuple(f)
        product = (1,)
        for f in factors:
            product = poly_mul(product, f, p)
        self.assertNotEqual(product, (1, 0, 12, 0, 1))

    def test_git_blob_and_source_manifest(self):
        self.assertEqual(blob_sha(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")
        self.assertEqual(len(PIN), 40)
        self.assertEqual(len(SOURCE), 5)
        self.assertTrue(all(len(sha) == 40 for _, sha, _ in SOURCE.values()))

    def test_output_not_a_lean_proof(self):
        for row in generate():
            self.assertFalse(row["full_upstream_Lean_witness_constructed"])
            self.assertIn(row["ell_mod12"], (1, 5, 7, 11))
            self.assertTrue(row["ImQ"])
            self.assertTrue(row["even_real_degree"])


if __name__ == "__main__":
    unittest.main()
