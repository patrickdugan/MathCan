"""BSAR-16E: exact quadratic interpolation remainder and dense core controls."""

from __future__ import annotations

import copy
import unittest

from experiments.bsar16.exact_residual import Q
from experiments.bsar16.float64_snapshots import COARSE_DT, certify_run
from experiments.bsar16.rational_enclosure import (
    add_field, polynomial_at, scale_field, taylor_data,
)
from experiments.bsar16.dense_interpolant import dense_run


class TestContinuousPolygonalEnclosure(unittest.TestCase):
    def test_quadratic_interpolation_remainder_exact_in_fourier_space(self) -> None:
        for n, phase, grid in ((1, -1, 16), (2, 1, 24)):
            coeffs, _, _ = taylor_data(n, phase, grid)
            for left, h in ((Q(0), Q(1, 1000)),
                            (Q(3, 1000), Q(1, 2000))):
                right, midpoint = left+h, left+h/2
                interpolated = add_field(
                    scale_field(polynomial_at(coeffs, left), Q(1, 2)),
                    scale_field(polynomial_at(coeffs, right), Q(1, 2)),
                )
                actual = polynomial_at(coeffs, midpoint)
                difference = add_field(interpolated, scale_field(actual, -1))
                expected = scale_field(coeffs[2], h*h/4)
                self.assertEqual(difference, expected)

    def test_full_interval_bounds_for_source_pinned_float_run(self) -> None:
        for n, phase in ((1, -1), (2, 1)):
            nodes = certify_run(n, phase, 16, COARSE_DT)
            result = dense_run(nodes)
            self.assertEqual(len(result["intervals"]), 12)
            self.assertEqual(result["dt_rational"], "1/1000")
            self.assertTrue(result["all_interval_direct_core_certified"])
            self.assertTrue(result["all_interval_via_galerkin_core_certified"])
            self.assertIn("piecewise-linear", result["scope"])
            for j, interval in enumerate(result["intervals"]):
                self.assertEqual(interval["interval_index"], j)
                self.assertEqual(Q(interval["time_left"]), COARSE_DT*j)
                self.assertEqual(Q(interval["time_right"]), COARSE_DT*(j+1))
                self.assertLessEqual(
                    Q(nodes["nodes"][j]["raw_binary64_to_rational_reference_L2_upper"]),
                    Q(interval["polygon_to_rational_reference_L2_upper"]),
                )
                self.assertLessEqual(
                    Q(nodes["nodes"][j+1]["raw_binary64_to_rational_reference_L2_upper"]),
                    Q(interval["polygon_to_rational_reference_L2_upper"]),
                )
                self.assertLessEqual(
                    Q(interval["polygon_to_rational_reference_L2_upper"]),
                    Q(interval["polygon_to_exact_galerkin_L2_upper"]),
                )
                self.assertGreater(
                    Q(interval["polygon_continuum_core_via_galerkin"][
                        "half_maximum_core_margin_lower"
                    ]), 0,
                )

    def test_corrupted_node_times_and_missing_snapshot_rejected(self) -> None:
        case = certify_run(1, 1, 16, COARSE_DT)
        bad = copy.deepcopy(case)
        bad["nodes"][1]["time"] = "1/7"
        with self.assertRaises(ValueError):
            dense_run(bad)
        bad = copy.deepcopy(case)
        bad["nodes"].pop()
        with self.assertRaises(ValueError):
            dense_run(bad)
        bad = copy.deepcopy(case)
        bad["cutoff_K"] = 100
        with self.assertRaises(ValueError):
            dense_run(bad)


if __name__ == "__main__":
    unittest.main()
