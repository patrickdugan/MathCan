"""Exact-math mutation and nonvacuity tests for RHD-08."""
import unittest
from itertools import combinations
from research.rh_proof_distillation.rhd08_coset_gate import (
    CONDUCTORS, classify, conductor_cert, conductor_result, cosets,
    generated, kernel, prime, units,
)


class CyclotomicFiberTests(unittest.TestCase):
    def test_conductor_unramified_relative_derivative(self):
        self.assertEqual(len(CONDUCTORS), 14)
        for n in CONDUCTORS:
            c = conductor_cert(n)
            self.assertTrue(c["real_degree_even"])
            self.assertTrue(c["relative_derivative_unit"])

    def test_degree_two_witnesses(self):
        for n, p, d, expected in ((20, 29, 1, 2), (24, 5, 1, 2), (21, 13, 3, 3)):
            x = classify(n, p, d)
            self.assertTrue(x["fieldok_arithmetic"])
            self.assertTrue(x["joint_arithmetic_gate"])
            self.assertEqual(x["residue_degree"], 2)
            self.assertEqual(x["fiber_size"], expected)
            self.assertTrue(x["oneK_distinct_pairs"])

    def test_fieldok_near_misses(self):
        for n, p, d in ((12, 5, 1), (12, 7, 3), (15, 7, 3)):
            x = classify(n, p, d)
            self.assertTrue(x["fieldok_arithmetic"])
            self.assertEqual(x["fiber_size"], 1)
            self.assertFalse(x["oneK_distinct_pairs"])
            self.assertFalse(x["joint_arithmetic_gate"])

    def test_noncyclic_galois_kernel_guarantees_pair(self):
        for n in CONDUCTORS:
            for d, m in ((1, 4), (3, 3)):
                if n % m:
                    continue
                c = conductor_result(n, d)
                H = kernel(n, d)
                self.assertEqual(c["H_order"], len(H))
                self.assertEqual(c["H_exponent"], max(len(generated(n, g)) for g in H))
                self.assertEqual(c["all_split_primes_have_OneK_pair"],
                                 c["H_exponent"] < c["H_order"])
                if c["H_exponent"] == c["H_order"]:
                    self.assertEqual(set(generated(n, c["counterexample_Frobenius_generator"])), set(H))

    def test_exact_coset_partition_and_contraction(self):
        for n in CONDUCTORS:
            for d, mod in ((1, 4), (3, 3)):
                if n % mod:
                    continue
                for ell in range(5, 200):
                    if not prime(ell) or n % ell == 0:
                        continue
                    x = classify(n, ell, d)
                    parts = [set(c) for c in x["E_prime_cosets"]]
                    self.assertEqual(set().union(*parts), set(units(n)))
                    self.assertEqual(x["G_order"], len(parts) * x["residue_degree"])
                    for a, b in combinations(parts, 2):
                        self.assertFalse(a & b)
                    self.assertEqual(x["fiber_size"], len(x["H"]) // len(set(x["H"]) & set(x["D"])))
                    self.assertEqual(bool(x["oneK_distinct_pairs"]), x["fiber_size"] > 1)
                    self.assertFalse(x["upstream_Lean_witness_proved"])

    def test_mutated_kernel_changes_contraction(self):
        x = classify(20, 29, 1)
        self.assertEqual(x["H"], [1, 9, 13, 17])
        self.assertEqual(x["D"], [1, 9])
        self.assertEqual(len(x["oneK_distinct_pairs"]), 2)
        self.assertNotEqual(kernel(20, 1), generated(20, 9))


if __name__ == "__main__":
    unittest.main()
