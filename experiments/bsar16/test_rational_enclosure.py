"""BSAR-16B rational dense-trajectory validation controls."""

from __future__ import annotations

import json
import unittest
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.bsar16.exact_residual import (
    GRID_SIZES, ROOTS, VISCOSITY, cutoff, exact_decomposition,
    squared_norm, source_modes,
)
from experiments.bsar16.rational_enclosure import (
    Q, TIME_END, add_field, audit, ceil_sqrt, enclosure,
    exp_upper, freeze, generate, high_polynomial, norm_squared,
    polynomial_at, projected_split, rhs_polynomial, round_up,
    scale_field, taylor_data,
)


class TestExactRationalTaylorEnvelope(unittest.TestCase):
    def test_defect_and_high_mode_polynomials_are_exact(self) -> None:
        # Independently evaluate nonlinear convolution at two rational times
        # and compare with the stored complete degree-four polynomials.
        for n, phase, grid in ((1, -1, 16), (2, 1, 24), (2, -1, 32)):
            kmax = cutoff(grid)
            poly, defect, residual = taylor_data(n, phase, grid)
            self.assertEqual(poly[0], source_modes(n, phase))
            self.assertFalse(defect[0])
            self.assertFalse(defect[1])
            self.assertEqual(len(defect), 5)
            self.assertEqual(len(residual), 5)
            self.assertEqual(
                norm_squared(residual[0]),
                exact_decomposition(poly[0], kmax)["high_residual_l2_squared"],
            )
            for t in (Q(1, 2000), Q(3, 250)):
                p = polynomial_at(poly, t)
                pdot = add_field(poly[1], scale_field(poly[2], 2*t))
                actual_rhs = rhs_polynomial([p], kmax, VISCOSITY)[0]
                direct_defect = add_field(pdot, scale_field(actual_rhs, -1))
                self.assertEqual(direct_defect, polynomial_at(defect, t))
                direct_high = projected_split(p, p, kmax)[1]
                self.assertEqual(direct_high, polynomial_at(residual, t))

    def test_fraction_square_root_and_exponential_bounds(self) -> None:
        for x in (Q(0), Q(1, 2), Q(2), Q(10, 7), Q(222, 17)):
            upper = ceil_sqrt(x)
            self.assertGreaterEqual(upper*upper, x)
            self.assertGreaterEqual(round_up(upper), upper)
        self.assertEqual(exp_upper(Q(0)), 1)
        self.assertEqual(exp_upper(Q(1, 2)), 2)
        self.assertEqual(exp_upper(Q(1)), 4)
        for x in (Q(-1),):
            with self.assertRaises(ValueError):
                exp_upper(x)
            with self.assertRaises(ValueError):
                ceil_sqrt(x)

    def test_all_source_roots_and_monotone_positive_certificates(self) -> None:
        rows, manifest = generate()
        self.assertEqual(len(rows), len(ROOTS)*len(GRID_SIZES))
        self.assertEqual(manifest["cases"], 12)
        self.assertIn("exact rational", manifest["validation"])
        for row in rows:
            n, phase, grid = row["frequency_N"], row["phase_sigma"], row["grid_M"]
            self.assertIn((n, phase), ROOTS)
            self.assertIn(grid, GRID_SIZES)
            expected = "1/34" if n == 2 and grid in (16, 24) else "0/1"
            self.assertEqual(row["initial_high_residual_L2_squared"], expected)
            self.assertEqual(row["polynomial_degree"], 2)
            self.assertEqual(row["defect_first_nonzero_degree_at_least"], 2)
            self.assertTrue(all(x >= 0 for x in [
                Q(c) for c in row["defect_upper_coefficients"]
            ]))
            for key in (
                "validated_galerkin_L2_error_upper",
                "validated_time_uniform_residual_L2_upper",
                "validated_time_uniform_gradient_Linfty_upper",
                "conditional_true_NSE_L2_error_upper_at_T",
            ):
                self.assertGreaterEqual(Q(row[key]), 0)
            self.assertIn("RK4", row["scope"])
            self.assertIn("conditional", row["scope"])
        for n, phase, grid in ((1, 1, 16), (2, -1, 24), (2, 1, 32)):
            short = enclosure(n, phase, grid, TIME_END/2)
            long = enclosure(n, phase, grid, TIME_END)
            for key in (
                "validated_galerkin_L2_error_upper",
                "validated_time_uniform_residual_L2_upper",
                "validated_time_uniform_gradient_Linfty_upper",
                "conditional_true_NSE_L2_error_upper_at_T",
            ):
                self.assertLessEqual(Q(short[key]), Q(long[key]))

    def test_source_validation_and_positive_time(self) -> None:
        with self.assertRaises(ValueError):
            enclosure(1, 1, 16, Q(0))
        with self.assertRaises(ValueError):
            enclosure(1, 1, 16, Q(-1, 100))
        with self.assertRaises(ValueError):
            enclosure(1, 1, 16, TIME_END, Q(0))
        with self.assertRaises(ValueError):
            taylor_data(3, 1, 16)
        with self.assertRaises(ValueError):
            polynomial_at([], Q(-1))
        with self.assertRaises(ValueError):
            projected_split(source_modes(0, 1), source_modes(1, 1), 5)

    def test_manifest_roundtrip_and_mutation_rejected(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = freeze(root)
            self.assertEqual(manifest, audit(root))
            rows = json.loads((root/"rows.json").read_text())
            rows[0]["validated_galerkin_L2_error_upper"] = "0/1"
            (root/"rows.json").write_text(json.dumps(rows))
            with self.assertRaises(ValueError):
                audit(root)


if __name__ == "__main__":
    unittest.main()
