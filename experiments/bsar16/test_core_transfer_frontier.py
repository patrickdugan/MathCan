"""BSAR-16I: independent exact obstruction and H4 core threshold checks."""

from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from experiments.bsar16.core_intervals import generate as original_core_generate
from experiments.bsar16.exact_residual import GRID_SIZES, ROOTS, Q
from experiments.bsar16.core_transfer_frontier import (
    CURL_EMBEDDING_UPPER,
    LATTICE_RADIUS,
    MIN_FULL_CORE_MARGIN,
    MIN_FULL_DIRECTION_GAP,
    M_VALUES,
    REGISTERED_H4_ERROR_UPPER,
    SOURCE_BSAR16C_ROWS_SHA256,
    _read_galerkin_archive,
    audit,
    c4_squared_upper,
    exact_high_frequency_obstruction,
    freeze,
    generate,
    transfer_certificate,
)


class TestExactLowL2HighCurlObstruction(unittest.TestCase):
    def test_all_registered_exact_source_anchors_excluded(self) -> None:
        for n, phase in ROOTS:
            last = Q(100)
            for m in (1, 2, 4, 8, 16, 32, 512):
                row = exact_high_frequency_obstruction(n, phase, m)
                self.assertTrue(row["divergence_free_mean_zero_real_smooth"])
                self.assertTrue(row["perturbation_curl_at_both_anchors_zero"])
                self.assertTrue(row["both_anchors_outside_new_true_half_core"])
                self.assertEqual(row["additional_wave_M"], 24*n*m)
                self.assertEqual(
                    Q(row["perturbation_velocity_L2_squared"]),
                    Q(1, 2*m*m),
                )
                self.assertEqual(
                    Q(row["curl_at_quarter_wave_point_magnitude"]), Q(24*n)
                )
                self.assertGreater(
                    Q(row["new_global_curl_max_strictly_greater_than"]),
                    2*Q(6*n)
                )
                self.assertLess(
                    Q(row["perturbation_velocity_L2_squared"]), last
                )
                last = Q(row["perturbation_velocity_L2_squared"])

    def test_invalid_obstruction_sources_fail(self) -> None:
        for n, phase, m in ((0, 1, 1), (1, 0, 1), (1, 2, 1),
                             (1, 1, 0), (2, -1, -2)):
            with self.assertRaises(ValueError):
                exact_high_frequency_obstruction(n, phase, m)


class TestH4LatticeAndCoreTransfer(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.records, cls.manifest = generate()

    def test_infinite_lattice_tail_exact_upper(self) -> None:
        bound = c4_squared_upper(LATTICE_RADIUS)
        self.assertEqual(LATTICE_RADIUS, 8)
        self.assertLess(bound, Q(9))
        self.assertGreater(bound, Q(0))
        self.assertLess(c4_squared_upper(16), c4_squared_upper(8))
        self.assertEqual(CURL_EMBEDDING_UPPER, Q(3))
        for radius in (0, -1):
            with self.assertRaises(ValueError):
                c4_squared_upper(radius)

    def test_all_original_galerkin_cases_and_uniform_conditional_gate(self) -> None:
        self.assertEqual(self.manifest["conditional_h4_core_cases"], 12)
        self.assertEqual(self.manifest["l2_obstruction_count"], 24)
        self.assertEqual(self.manifest["source_bsar16c_rows_sha256"],
                         SOURCE_BSAR16C_ROWS_SHA256)
        self.assertEqual(
            self.manifest["uniform_H4_velocity_error_threshold"], "1/20"
        )
        self.assertFalse(self.manifest["conditional_full_PDE_H4_error_proved"])
        self.assertFalse(
            self.manifest["independent_full_PDE_existence_through_T_proved"]
        )
        rows = self.records[0]["transfers"]
        self.assertEqual(len(rows), 12)
        self.assertEqual(
            {(r["frequency_N"], r["phase_sigma"], r["grid_M"]) for r in rows},
            {(n, phase, grid) for n, phase in ROOTS for grid in GRID_SIZES},
        )
        for row in rows:
            n = row["frequency_N"]
            self.assertEqual(row["time_horizon"], "3/250")
            self.assertGreater(
                Q(row["conditional_full_half_core_margin_lower"]),
                MIN_FULL_CORE_MARGIN,
            )
            self.assertGreater(
                Q(row["conditional_full_direction_gap_lower"]),
                MIN_FULL_DIRECTION_GAP,
            )
            self.assertGreater(
                Q(row["conditional_full_cone_lower"]),
                Q(row["simple_uniform_full_cone_lower"]),
            )
            self.assertEqual(
                Q(row["simple_uniform_full_cone_lower"]),
                Q(56*n, 275),
            )
            self.assertTrue(row["full_core_condition_met_if_H4_bound_proved"])
            self.assertFalse(row["full_PDE_H4_error_bound_proved"])

    def test_negative_overlarge_errors_and_mutated_source_custody(self) -> None:
        core_rows, _ = _read_galerkin_archive()
        source = core_rows[0]
        with self.assertRaises(ValueError):
            transfer_certificate(source, Q(1, 10))
        with self.assertRaises(ValueError):
            transfer_certificate(source, Q(-1))
        bad = copy.deepcopy(source)
        bad["half_maximum_core_margin_lower"] = "1/2"
        with self.assertRaises(ArithmeticError):
            transfer_certificate(bad, REGISTERED_H4_ERROR_UPPER)
        bad = copy.deepcopy(source)
        bad["max_vorticity_perturbation_upper"] = "2/1"
        with self.assertRaises(ArithmeticError):
            transfer_certificate(bad, REGISTERED_H4_ERROR_UPPER)
        with patch("experiments.bsar16.core_transfer_frontier.core_generate",
                   return_value=([], {"rows_sha256": "wrong"})):
            _read_galerkin_archive.cache_clear()
            with self.assertRaisesRegex(ValueError, "archive changed"):
                generate()
        _read_galerkin_archive.cache_clear()

    def test_frozen_replay_and_tampering(self) -> None:
        with TemporaryDirectory() as directory:
            out = Path(directory)
            frozen = freeze(out)
            self.assertEqual(self.manifest, frozen)
            import hashlib
            self.assertEqual(hashlib.sha256((out/"rows.json").read_bytes()).hexdigest(), frozen["rows_sha256"])
            self.assertEqual(audit(out), frozen)
            rows = json.loads((out/"rows.json").read_text())
            rows[0]["transfers"][0]["full_PDE_H4_error_bound_proved"] = True
            (out/"rows.json").write_text(json.dumps(rows))
            with self.assertRaises(ValueError):
                audit(out)


if __name__ == "__main__":
    unittest.main()
