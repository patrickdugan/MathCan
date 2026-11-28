"""Independent finite-ring receipts for RHD-10C unit obstruction."""
from __future__ import annotations

import hashlib
from pathlib import Path
import tempfile
import unittest

from research.rh_proof_distillation.rhd09_local_character import P, P2
from research.rh_proof_distillation.rhd10_unit_obstruction import (
    FACTORS, UNIT_EXPONENTS, cyclotomic_unit, determinant, local_norm,
    mul, obstruction_receipt, power, principal_log_vector, write_report,
)


class RHD10UnitObstructionTests(unittest.TestCase):
    def test_unit_norm_and_local_logs(self):
        # Exact residues, independently frozen against regression.
        expected = (
            ((13, 14), (0, 28)),
            ((17, 23), (20, 3)),
            ((14, 23), (7, 3)),
            ((14, 14), (2, 28)),
        )
        for j, factor in enumerate(FACTORS):
            units = [cyclotomic_unit(factor, k) for k in UNIT_EXPONENTS]
            actual = tuple(principal_log_vector(factor, u) for u in units)
            self.assertEqual(actual, expected[j])
            self.assertTrue(all(local_norm(factor, u) % P for u in units))
            self.assertEqual(determinant(*actual), (16, 26, 26, 16)[j])

    def test_no_nonzero_linear_character_annihilates_both_units(self):
        for factor in FACTORS:
            logs = [principal_log_vector(factor, cyclotomic_unit(factor, k))
                    for k in UNIT_EXPONENTS]
            for a in range(P):
                for b in range(P):
                    if a == b == 0:
                        continue
                    self.assertTrue(
                        any((a*x + b*y) % P != 0 for x, y in logs),
                        (factor, (a, b), logs),
                    )

    def test_log_homomorphism_and_unit_order(self):
        for factor in FACTORS:
            u = cyclotomic_unit(factor, 1)
            v = cyclotomic_unit(factor, 3)
            w = mul(factor, u, v)
            a = principal_log_vector(factor, u)
            b = principal_log_vector(factor, v)
            self.assertEqual(
                principal_log_vector(factor, w),
                tuple((x+y) % P for x, y in zip(a, b)),
            )
            self.assertEqual(power(factor, (1, 0), P2), (1, 0))
            self.assertEqual(local_norm(factor, (1, 0)), 1)

    def test_norm_products_and_cross_place_cancellation(self):
        report = obstruction_receipt()
        self.assertEqual(report["unit_norms_globally"], [1, 1])
        self.assertEqual(report["local_character_sums_mod_29"], [0, 0])
        self.assertEqual(
            [p["determinant_mod_29"] for p in report["places"]],
            [16, 26, 26, 16],
        )
        self.assertFalse(report["lean_witness_proved"])
        self.assertFalse(report["automorphic_witness_proved"])

    def test_byte_for_byte_manifest(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / "unit_obstruction.json"
            first = write_report(output)
            data = output.read_bytes()
            self.assertEqual(first, write_report(output))
            self.assertEqual(data, output.read_bytes())
            self.assertEqual(
                output.with_suffix(".sha256").read_text().split()[0],
                hashlib.sha256(data).hexdigest(),
            )


if __name__ == "__main__":
    unittest.main()
