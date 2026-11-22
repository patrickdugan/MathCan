"""BSAR-15: source-pinned dealiased Galerkin tests and observation boundary."""

from __future__ import annotations

import json
import math
import unittest
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory

import numpy as np

from experiments.bsar15.galerkin import (
    AMPLITUDE,
    COARSE_DT,
    FINE_DT,
    GRIDS,
    SCENARIOS,
    T_END,
    VISCOSITY,
    FourierGalerkin,
    campaign,
    freeze,
)
from scripts.bsar14_initial_triad_transfer import (
    convolution as exact_convolution,
    modes as exact_modes,
    pressure_projection as exact_projection,
)


class TestInitialSourceProjection(unittest.TestCase):
    def test_exact_gaussian_source_and_spectral_energy(self) -> None:
        for n, phase in SCENARIOS:
            solver = FourierGalerkin(24, n, phase)
            field = solver.initial
            self.assertEqual(solver.cutoff, 7)
            self.assertEqual(len(solver.modes), 8)
            self.assertTrue(np.max(np.abs(field[:, ~solver.mask])) == 0)
            self.assertAlmostEqual(solver.energy(field), 2, places=12)
            self.assertAlmostEqual(solver.enstrophy(field), 15.5 * n*n, places=12)
            self.assertLess(
                np.max(np.abs(np.sum(solver.k * field, axis=0))), 1e-13
            )
            for wave, vector in exact_modes(n, AMPLITUDE, phase).items():
                index = tuple(x % solver.grid for x in wave)
                expected = np.array([complex(float(x.real), float(x.imag))
                                     for x in vector])
                np.testing.assert_allclose(
                    field[(slice(None), *index)], expected, atol=1e-14
                )

    def test_nonlinear_derivative_and_conservation_match_exact_oracle(self) -> None:
        for n, phase in SCENARIOS:
            solver = FourierGalerkin(24, n, phase)
            projected = solver.nonlinear_hat(solver.initial)
            _, exact = exact_projection(exact_convolution(solver.modes))
            for wave, vector in exact.items():
                if max(abs(x) for x in wave) > solver.cutoff:
                    continue
                index = tuple(x % solver.grid for x in wave)
                expected = [complex(float(x.real), float(x.imag)) for x in vector]
                np.testing.assert_allclose(
                    projected[(slice(None), *index)], expected, atol=1e-12
                )
            new_mode = projected[:, n, 0, n]
            np.testing.assert_allclose(
                new_mode, np.array([0j, 1j*n/4, 0j]), atol=1e-12
            )
            np.testing.assert_allclose(
                solver.rhs(solver.initial)[:, n, 0, n],
                np.array([0j, -1j*n/4, 0j]), atol=1e-12
            )
            transfers = solver.shell_transfer(solver.initial)
            expected = {"1": phase*n/4, "4": -phase*n, "5": phase*3*n/4}
            for shell, value in expected.items():
                self.assertAlmostEqual(transfers[shell], value, places=11)
            self.assertAlmostEqual(sum(transfers.values()), 0, places=11)
            nonlinear_energy = np.real(
                np.sum(np.conj(solver.initial) * projected)
            )
            self.assertAlmostEqual(nonlinear_energy, 0.0, places=11)

    def test_projection_and_dealiasing_controls(self) -> None:
        solver = FourierGalerkin(16, 2, 1)
        rng = np.random.default_rng(1314)
        junk = rng.normal(size=solver.initial.shape) + 1j * rng.normal(
            size=solver.initial.shape
        )
        cleaned = solver.project(junk)
        self.assertLess(
            np.max(np.abs(np.sum(solver.k * cleaned, axis=0))), 1e-11
        )
        self.assertEqual(float(np.max(np.abs(cleaned[:, ~solver.mask]))), 0.0)
        self.assertEqual(float(np.max(np.abs(cleaned[:, 0, 0, 0]))), 0.0)
        # Removing the pressure projection changes the source's non-gradient
        # convective acceleration, even though its total energy derivative is 0.
        initial = FourierGalerkin(16, 1, 1)
        projected = initial.nonlinear_hat(initial.initial)
        self.assertGreater(float(np.linalg.norm(projected)), 0.1)

    def test_invalid_grid_time_and_source_arguments(self) -> None:
        for grid, n, phase in ((12, 2, 1), (17, 1, 1), (16, 0, 1),
                               (16, 1, 0), (16, 1, 2)):
            with self.assertRaises(ValueError):
                FourierGalerkin(grid, n, phase)
        solver = FourierGalerkin(16, 1, -1)
        for dt, horizon in ((0, 0.01), (-1, 0.01), (0.004, 0.01)):
            with self.assertRaises(ValueError):
                solver.run(dt, horizon)


class TestShortTimeCampaign(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = campaign()

    def test_scenario_matrix_and_phase_symmetry(self) -> None:
        report = self.report
        self.assertEqual(report["run_count"], 16)
        self.assertEqual(report["phase_matched_roots"], 2)
        self.assertEqual(
            {(r["mode_n"], r["phase"]) for r in report["runs"]}, set(SCENARIOS)
        )
        for n, phase in SCENARIOS:
            subset = [r for r in report["runs"]
                      if r["mode_n"] == n and r["phase"] == phase]
            self.assertEqual(sorted(x["grid"] for x in subset), [16, 24, 32, 32])
            self.assertEqual(
                sorted(x["dt"] for x in subset),
                [FINE_DT, COARSE_DT, COARSE_DT, COARSE_DT],
            )
            initial = subset[0]["diagnostics"][0]
            self.assertAlmostEqual(initial["energy"], 2.0, places=9)
            self.assertAlmostEqual(initial["enstrophy"], 15.5*n*n, places=9)

    def test_viscous_energy_balance_and_divergence(self) -> None:
        for run in self.report["runs"]:
            snapshots = run["diagnostics"]
            self.assertEqual(len(snapshots), 3)
            self.assertTrue(all(
                s["energy"] <= snapshots[0]["energy"] + 1e-9
                for s in snapshots
            ))
            self.assertGreater(run["dissipation_integral_trapezoid"], 0)
            self.assertLess(abs(run["energy_defect_trapezoid"]), 1e-5)
            self.assertLess(run["max_divergence_hat"], 1e-10)
            self.assertTrue(all(
                abs(s["nonlinear_energy_power"]) < 1e-10 for s in snapshots
            ))
            for snapshot in snapshots:
                self.assertLess(snapshot["divergence_hat_max"], 1e-10)
                self.assertGreater(snapshot["enstrophy"], 0)

    def test_generated_mode_and_short_time_linear_lead(self) -> None:
        for run in self.report["runs"]:
            n = run["mode_n"]
            horizon = run["t_end"]
            final = run["diagnostics"][-1]
            actual = complex(*final["new_mode_velocity_y"])
            predicted = -1j * n*horizon/4
            self.assertGreater(abs(actual), 0.0)
            self.assertLess(abs(actual - predicted), abs(predicted)*0.12)
            self.assertAlmostEqual(
                final["new_mode_vector_norm"], abs(actual),
                delta=abs(actual)*0.05,
            )
            self.assertTrue(run["all_initial_shell_transfer_signs_persist"])
            self.assertEqual(
                run["sign_flip_first_time"], {"1": None, "4": None, "5": None}
            )

    def test_core_witness_and_grid_sampling_custody(self) -> None:
        for run in self.report["runs"]:
            for snap in run["diagnostics"]:
                core = snap["core"]
                self.assertTrue(core["true_core_anchor_pair_by_galerkin_max_upper"])
                self.assertGreater(core["anchor_continuum_cone_lower_if_valid"], 0)
                self.assertGreater(
                    core["galerkin_cone_upper_from_lipschitz"],
                    core["anchor_continuum_cone_lower_if_valid"],
                )
                self.assertGreater(core["sampled_grid_relative_cone_K"], 0)
                self.assertGreater(core["grid_core_sample_pair_count"], 0)
                self.assertGreater(core["grid_core_fraction"], 0.0)
                self.assertLessEqual(core["grid_core_fraction"], 1.0)
                self.assertIn("no certified outward rounding", core["rounding_scope"])

    def test_resolution_and_dt_differences_are_reported_not_certified(self) -> None:
        self.assertEqual(len(self.report["grid_time_comparisons"]), 4)
        for summary in self.report["grid_time_comparisons"]:
            self.assertLess(summary["temporal_energy_abs_diff"], 1e-4)
            self.assertLess(summary["temporal_new_mode_y_abs_diff"], 1e-4)
            self.assertLess(summary["spatial_energy_abs_diff_grid24_32"], 0.05)
            self.assertLess(summary["spatial_new_mode_y_abs_diff_grid24_32"], 0.05)
            self.assertTrue(summary["all_reference_anchor_core_guarantees"])
            self.assertTrue(summary["reference_time_series_shell_sign_persistence"])
        self.assertIn("NO rigorous", self.report["disclaimer"])

    def test_freeze_receipts_stable_and_source_pinned(self) -> None:
        # A separate call also exercises the on-disk SHA manifest and report.
        with TemporaryDirectory() as directory:
            root = Path(directory)
            meta = freeze(root)
            self.assertEqual(meta["run_count"], 16)
            self.assertEqual(
                meta["source_exact_mathcan"],
                "e2c0e1c56f6e5d2291536156709f75668d1e0f8f",
            )
            data = (root / "runs.json").read_bytes()
            self.assertEqual(
                __import__("hashlib").sha256(data).hexdigest(),
                meta["run_sha256"],
            )
            self.assertEqual(len(json.loads(data)), 16)
            self.assertEqual(len(json.loads((root / "comparisons.json").read_text())), 4)


if __name__ == "__main__":
    unittest.main()
