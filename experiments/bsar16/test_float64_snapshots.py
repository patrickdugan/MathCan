"""BSAR-16D exact-binary64 snapshot and source-pinned Galerkin audit."""

from __future__ import annotations

import math
import unittest
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory

import numpy as np

from experiments.bsar15.galerkin import FourierGalerkin
from experiments.bsar16.exact_residual import Q, encode, source_modes
from experiments.bsar16.rational_enclosure import (
    ceil_sqrt, enclosure, gradient_l1, norm_squared, polynomial_at, taylor_data,
)
from experiments.bsar16.float64_snapshots import (
    COARSE_DT, FINE_DT, T_END, _ceil_abs_float_minus_fraction,
    _galerkin_error_upper, certify_run, snapshot_reference_distance_upper,
)


class TestBinary64ExactComparison(unittest.TestCase):
    def test_binary64_coordinates_bounded_as_exact_rationals(self) -> None:
        # These are full finite binary representations, including a tiny
        # FFT-like residual with a large power-of-two denominator.
        for actual, target in (
            (0.1, Q(1, 10)),
            (2.0**-1000, Q(0)),
            (-0.0, Q(0)),
            (-1.25, Q(-5, 4)),
            (2.0**-40, Q(1, 1000000)),
        ):
            scale = 10**15
            count = _ceil_abs_float_minus_fraction(actual, target, scale)
            self.assertGreaterEqual(Q(count, scale),
                                    abs(Q(*actual.as_integer_ratio())-target))
            self.assertLess(Q(count, scale)-
                            abs(Q(*actual.as_integer_ratio())-target),
                            Q(1, scale)+Q(1, 10**100))
        with self.assertRaises(ValueError):
            _ceil_abs_float_minus_fraction(math.inf, Q(0), 10**15)
        with self.assertRaises(ValueError):
            _ceil_abs_float_minus_fraction(math.nan, Q(0), 10**15)

    def test_full_cube_initial_data_exact_and_one_bit_mutation_visible(self) -> None:
        solver = FourierGalerkin(16, 2, 1)
        exact = source_modes(2, 1)
        self.assertEqual(snapshot_reference_distance_upper(
            solver, solver.initial, exact), Q(0))
        altered = solver.initial.copy()
        altered[0, 1, 0, 0] += 2.0**-40
        upper = snapshot_reference_distance_upper(solver, altered, exact)
        self.assertGreaterEqual(upper, Q(1, 2**40))
        self.assertLess(upper, Q(1, 2**40)+Q(1, 10**12))

    def test_invalid_spectral_inputs_fail_closed(self) -> None:
        solver = FourierGalerkin(16, 1, 1)
        hats = solver.initial.copy()
        outside = hats.copy()
        outside[0, 7, 0, 0] = 1j
        with self.assertRaises(ValueError):
            snapshot_reference_distance_upper(solver, outside, source_modes(1, 1))
        nan_coeff = hats.copy()
        nan_coeff[0, 1, 0, 0] = complex(float("nan"), 0)
        with self.assertRaises(ValueError):
            snapshot_reference_distance_upper(solver, nan_coeff, source_modes(1, 1))
        bad_mean = hats.copy()
        bad_mean[0, 0, 0, 0] = 1
        with self.assertRaises(ValueError):
            snapshot_reference_distance_upper(solver, bad_mean, source_modes(1, 1))
        with self.assertRaises(ValueError):
            snapshot_reference_distance_upper(solver, hats.astype(np.complex64),
                                              source_modes(1, 1))
        with self.assertRaises(ValueError):
            snapshot_reference_distance_upper(solver, hats, source_modes(1, 1),
                                              coordinate_scale=0)

    def test_rational_error_envelope_matches_bsar16b(self) -> None:
        for n, phase, grid in ((1, -1, 16), (2, 1, 24)):
            poly, defect, _ = taylor_data(n, phase, grid)
            d = [ceil_sqrt(norm_squared(x)) for x in defect]
            g = [gradient_l1(x) for x in poly]
            self.assertEqual(_galerkin_error_upper(Q(0), d, g), Q(0))
            for t in (Q(1, 1000), T_END):
                bounded = _galerkin_error_upper(t, d, g)
                registered = enclosure(n, phase, grid, horizon=t)
                self.assertLessEqual(
                    bounded, Q(registered["validated_galerkin_L2_error_upper"])
                )
                self.assertGreater(bounded, 0)

    def test_selected_actual_rk4_time_node_certificates(self) -> None:
        # Every intermediate floating state is replayed and audited.
        for n, phase, grid, dt in (
            (1, -1, 16, COARSE_DT),
            (2, 1, 16, COARSE_DT),
        ):
            case = certify_run(n, phase, grid, dt)
            self.assertEqual(case["steps"], 12)
            self.assertEqual(len(case["nodes"]), 13)
            self.assertEqual(case["nodes"][0]["tick"], 0)
            self.assertEqual(case["nodes"][0]["time"], "0/1")
            self.assertEqual(
                case["nodes"][0]["raw_binary64_to_rational_reference_L2_upper"],
                "0/1"
            )
            self.assertEqual(case["nodes"][-1]["time"], encode(T_END))
            self.assertTrue(case["all_nodes_interpreted_core_certified"])
            self.assertGreater(float(case["final_numerical_energy_float64"]), 1.5)
            for node in case["nodes"]:
                self.assertLessEqual(
                    Q(node["raw_binary64_to_rational_reference_L2_upper"]),
                    Q(node["snapshot_to_exact_galerkin_L2_upper"]),
                )
                self.assertGreater(
                    Q(node["interpreted_snapshot_core"]["half_maximum_core_margin_lower"]),
                    0,
                )
        with self.assertRaises(ValueError):
            certify_run(2, 1, 24, FINE_DT)


if __name__ == "__main__":
    unittest.main()
