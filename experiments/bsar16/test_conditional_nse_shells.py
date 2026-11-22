"""BSAR-16G: conditional full-NSE low-shell sign and source controls."""

from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.bsar16.exact_residual import GRID_SIZES, ROOTS, Q
from experiments.bsar16.rational_enclosure import (
    TIME_END, enclosure as rational_pde_enclosure,
)
from experiments.bsar16.shell_signs import SHELLS, _basis
from experiments.bsar16.conditional_nse_shells import (
    _conditional_gap, audit, certify, freeze, generate, round_down,
)


class TestConditionalSmoothNSEShellSigns(unittest.TestCase):
    def test_exact_source_and_conditional_l2_hypothesis(self) -> None:
        for n, phase, grid in (
            (1, -1, 16), (1, 1, 32), (2, -1, 24), (2, 1, 32)
        ):
            basis = _basis(n, phase, grid)
            source = rational_pde_enclosure(n, phase, grid)
            self.assertEqual(source["time_horizon"], "3/250")
            self.assertEqual(source["viscosity"], "1/10")
            self.assertIn("conditional", source["scope"])
            for shell in SHELLS:
                gap, ref, error, combined, y, z = _conditional_gap(
                    basis, n, phase, grid, shell, TIME_END, source
                )
                self.assertEqual(gap, ref-error)
                self.assertGreater(z, 0)
                self.assertGreater(combined, z)
                self.assertGreater(combined, y)
                self.assertGreater(ref, 0)
                self.assertGreater(error, 0)
                self.assertGreater(gap, 0)

    def test_all_smooth_conditional_sign_certificates_and_margin(self) -> None:
        rows, manifest = generate()
        self.assertEqual(len(rows), len(ROOTS)*len(GRID_SIZES))
        self.assertEqual(manifest["case_count"], 12)
        self.assertEqual(manifest["conditional_shell_certificates"], 36)
        for row in rows:
            n, phase, grid = (
                row["frequency_N"], row["phase_sigma"], row["grid_M"]
            )
            self.assertIn((n, phase), ROOTS)
            self.assertIn(grid, GRID_SIZES)
            self.assertIn("smooth", row["PDE_hypothesis"])
            basis = _basis(n, phase, grid)
            for shell in row["shells"]:
                duration = Q(shell["certified_duration_if_smooth"])
                self.assertGreater(duration, 0)
                self.assertLessEqual(duration, TIME_END)
                self.assertTrue(shell["conditional_smooth_nse_existence_required"])
                self.assertEqual(
                    shell["full_T_conditional_sign_certified"],
                    duration == TIME_END
                )
                source = rational_pde_enclosure(
                    n, phase, grid, horizon=duration
                )
                gap, ref, error, combined, y, z = _conditional_gap(
                    basis, n, phase, grid,
                    shell["shell_normalized"], duration, source
                )
                self.assertGreater(gap, 0)
                self.assertEqual(
                    Q(shell["original_signed_transfer"]),
                    basis["transfers"][shell["shell_normalized"]][0]
                )
                self.assertLessEqual(
                    Q(shell["conditional_full_NSE_signed_transfer_lower"]), gap
                )
                self.assertGreater(
                    Q(shell["conditional_full_NSE_signed_transfer_lower"]), 0
                )
                self.assertGreaterEqual(
                    Q(shell["finite_shell_transfer_error_upper"]), error
                )
                self.assertGreaterEqual(
                    Q(shell["full_NSE_to_rational_reference_L2_upper"]), combined
                )
                self.assertLessEqual(
                    Q(shell["reference_signed_transfer_lower"]), ref
                )
                self.assertGreaterEqual(
                    Q(shell["full_NSE_to_galerkin_L2_upper"]), z
                )
                self.assertGreaterEqual(
                    Q(shell["galerkin_to_rational_reference_L2_upper"]), y
                )
        self.assertEqual(
            manifest["cases_full_T_conditionally_certified"],
            sum(row["all_three_shells_conditional_full_T"] for row in rows),
        )

    def test_wrong_source_fails_and_inflated_pde_error_removes_gate(self) -> None:
        n, phase, grid = 2, -1, 24
        basis = _basis(n, phase, grid)
        source = rational_pde_enclosure(n, phase, grid)
        bad = copy.deepcopy(source)
        bad["phase_sigma"] = -phase
        with self.assertRaises(ValueError):
            _conditional_gap(basis, n, phase, grid, 1, TIME_END, bad)
        bad = copy.deepcopy(source)
        bad["viscosity"] = "0/1"
        with self.assertRaises(ValueError):
            _conditional_gap(basis, n, phase, grid, 1, TIME_END, bad)
        bad = copy.deepcopy(source)
        bad["conditional_true_NSE_L2_error_upper_at_T"] = "100/1"
        gap, _, _, _, _, _ = _conditional_gap(
            basis, n, phase, grid, 1, TIME_END, bad
        )
        self.assertLess(gap, 0)
        with self.assertRaises(ValueError):
            _conditional_gap(basis, n, phase, grid, 1, Q(1, 100), source)

    def test_directed_rational_bounds_and_archive_tamper_rejection(self) -> None:
        self.assertLessEqual(round_down(Q(-1, 13)), Q(-1, 13))
        self.assertLessEqual(round_down(Q(11, 13)), Q(11, 13))
        with self.assertRaises(ValueError):
            round_down(Q(1), 0)
        with TemporaryDirectory() as directory:
            root = Path(directory)
            actual = freeze(root)
            self.assertEqual(actual, audit(root))
            rows = json.loads((root/"rows.json").read_text())
            rows[0]["shells"][0]["conditional_full_NSE_signed_transfer_lower"] = "0/1"
            (root/"rows.json").write_text(json.dumps(rows))
            with self.assertRaises(ValueError):
                audit(root)


if __name__ == "__main__":
    unittest.main()
