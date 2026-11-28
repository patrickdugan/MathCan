from __future__ import annotations
import unittest
from fractions import Fraction
from research.continuity_v1.adapter_succession import (
    AdapterStep, audit_succession, bilinear_margin, bilinear_step,
)


class AdapterSuccessionTests(unittest.TestCase):
    def test_bilinear_compound_effect(self):
        self.assertEqual(bilinear_margin(0, 0), Fraction(1, 4))
        self.assertEqual(bilinear_margin(1, 0), Fraction(1, 4))
        self.assertEqual(bilinear_margin(0, 1), Fraction(1, 4))
        self.assertEqual(bilinear_margin(1, 1), Fraction(-3, 4))
        receipt = audit_succession([
            bilinear_step("base", "adapt-a", (0, 0), (1, 0)),
            bilinear_step("adapt-a", "adapt-ab", (1, 0), (1, 1)),
        ])
        self.assertEqual(receipt.realized_loss, 1)
        self.assertEqual(receipt.total_declared_loss, 2)
        self.assertFalse(receipt.conditionally_preserves_positive)
        self.assertFalse(receipt.actually_positive)
        self.assertEqual(receipt.checkpoint_path, ("base", "adapt-a", "adapt-ab"))

    def test_positive_affine_path(self):
        steps = [
            AdapterStep("w0", "w1", Fraction(5, 2), Fraction(2),
                        Fraction(-1, 2), Fraction(0), Fraction(1)),
            AdapterStep("w1", "w2", Fraction(2), Fraction(3, 2),
                        Fraction(-1, 2), Fraction(0), Fraction(1)),
        ]
        result = audit_succession(steps)
        self.assertEqual(result.total_declared_loss, 1)
        self.assertEqual(result.residual_slack, 0)
        self.assertTrue(result.conditionally_preserves_positive)
        self.assertTrue(result.actually_positive)
        self.assertEqual(result.public()["assurance"],
                         "declared-local-bounds; neural Hessian premise is unverified")

    def test_zero_margin_threshold_is_strict(self):
        receipt = audit_succession([
            AdapterStep("a", "b", 1, 0, 1, 0, 1),
        ])
        self.assertFalse(receipt.conditionally_preserves_positive)
        self.assertFalse(receipt.actually_positive)

    def test_rejects_wrong_margin_transition(self):
        with self.assertRaisesRegex(ValueError, "checkpoint or margin"):
            audit_succession([
                AdapterStep("a", "b", 2, 1, 1, 0, 1),
                AdapterStep("b", "c", 2, 1, 1, 0, 1),
            ])
        with self.assertRaisesRegex(ValueError, "checkpoint or margin"):
            audit_succession([
                AdapterStep("a", "b", 2, 1, 1, 0, 1),
                AdapterStep("d", "c", 1, 0, 1, 0, 1),
            ])

    def test_rejects_falsified_step_bound(self):
        with self.assertRaisesRegex(ValueError, "violates"):
            audit_succession([AdapterStep("a", "b", 1, -1, 0, 0, 1)])

    def test_rejects_invalid_bounds_or_float(self):
        with self.assertRaises(ValueError):
            audit_succession([AdapterStep("a", "b", 1, 0, 0, -1, 1)])
        with self.assertRaises(TypeError):
            audit_succession([AdapterStep("a", "b", 1.0, 0, 1, 0, 1)])
        with self.assertRaises(ValueError):
            audit_succession([])


if __name__ == "__main__":
    unittest.main()
