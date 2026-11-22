"""BSAR-16J-A exact initial residual and Fourier norm tests."""

from __future__ import annotations

import hashlib
import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.bsar16.exact_residual import (
    GRID_SIZES, ROOTS, Q, cutoff, exact_decomposition, source_modes,
)
from experiments.bsar16.initial_wiener_tangent import (
    NONZERO_HIGH_K, audit, exact_sqrt, freeze, generate, source_tangent,
)
from scripts.bsar14_initial_triad_transfer import (
    convolution as source_convolution,
    modes as original_modes,
    pressure_projection as original_projection,
)


class TestInitialWienerTangent(unittest.TestCase):
    def test_original_exact_projection_and_nonzero_pair(self) -> None:
        for n, phase in ROOTS:
            native = original_modes(n, Q(1), phase)
            _, original = original_projection(source_convolution(native))
            for grid in GRID_SIZES:
                kmax = cutoff(grid)
                high = exact_decomposition(source_modes(n, phase), kmax)[
                    "high_residual"
                ]
                for k, v in high.items():
                    self.assertIn(k, original)
                    self.assertEqual(
                        [(x.real, x.imag) for x in v],
                        [(x.real, x.imag) for x in original[k]],
                    )
                if n == 2 and grid in (16, 24):
                    self.assertEqual(set(high), set(NONZERO_HIGH_K))
                else:
                    self.assertFalse(high)

    def test_exact_mode_norms_and_source_pinned_tangent(self) -> None:
        rows, manifest = generate()
        self.assertEqual(len(rows), 12)
        self.assertEqual(manifest["nonzero_high_mode_cases"], 4)
        self.assertEqual(
            {(r["frequency_N"], r["phase_sigma"], r["grid_M"])
             for r in rows},
            {(n, phase, grid)
             for n, phase in ROOTS for grid in GRID_SIZES},
        )
        for row in rows:
            active = row["frequency_N"] == 2 and row["grid_M"] in (16, 24)
            self.assertEqual(row["nonzero_initial_high_defect"], active)
            expected = {
                "source_high_mode_L2_squared": Q(1, 34),
                "source_high_mode_A1_wiener_norm": Q(2),
                "source_high_mode_curl_L2_squared": Q(2),
                "source_high_mode_velocity_H4_squared": Q(69**4, 34),
            } if active else {
                "source_high_mode_L2_squared": Q(0),
                "source_high_mode_A1_wiener_norm": Q(0),
                "source_high_mode_curl_L2_squared": Q(0),
                "source_high_mode_velocity_H4_squared": Q(0),
            }
            for key, value in expected.items():
                self.assertEqual(Q(row[key]), value)
            self.assertFalse(row["future_full_PDE_curl_bound_proved"])
            self.assertFalse(row["future_full_PDE_H4_bound_proved"])
            self.assertFalse(row["full_PDE_smooth_through_T_proved"])
            self.assertEqual(row["time_scope"],
                             "exact t=0 tangent only for local smooth full NSE")

    def test_rational_square_roots_and_invalid_inputs(self) -> None:
        for q in (Q(0), Q(1), Q(4, 9), Q(49, 25)):
            self.assertEqual(exact_sqrt(q)**2, q)
        with self.assertRaises(ArithmeticError):
            exact_sqrt(Q(2))
        with self.assertRaises(ValueError):
            exact_sqrt(Q(-1, 2))
        for n, phase, grid in ((0, 1, 16), (2, 0, 16),
                                (1, -1, 17), (3, 1, 24)):
            with self.assertRaises(ValueError):
                source_tangent(n, phase, grid)

    def test_archive_hash_and_negative_mutation(self) -> None:
        with TemporaryDirectory() as folder:
            root = Path(folder)
            manifest = freeze(root)
            blob = (root/"rows.json").read_bytes()
            self.assertEqual(hashlib.sha256(blob).hexdigest(),
                             manifest["rows_sha256"])
            self.assertEqual(audit(root), manifest)
            rows = json.loads(blob)
            rows[0]["source_high_mode_A1_wiener_norm"] = "1/1"
            (root/"rows.json").write_text(json.dumps(rows))
            with self.assertRaises(ValueError):
                audit(root)


if __name__ == "__main__":
    unittest.main()
