"""BSAR-16A exact spatial forcing and finite Galerkin energy controls."""

from __future__ import annotations

import json
import unittest
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.bsar16.exact_residual import (
    Gaussian, ROOTS, GRID_SIZES, VISCOSITY, audit, cutoff,
    exact_decomposition, freeze, generate, leray, nonlinear,
    opposite, source_modes, validate_field,
)
from scripts.bsar14_initial_triad_transfer import (
    convolution as original_convolution,
    modes as original_modes,
    pressure_projection as original_projection,
)

Q = Fraction


class ExactSourceParity(unittest.TestCase):
    def test_modes_and_all_projected_convolutions_agree_with_bsar14(self) -> None:
        for n, phase in ROOTS:
            ours = source_modes(n, phase)
            theirs = original_modes(n, Q(1), phase)
            self.assertEqual(set(ours), set(theirs))
            for k, vector in ours.items():
                self.assertEqual(
                    [(z.real, z.imag) for z in vector],
                    [(z.real, z.imag) for z in theirs[k]],
                )
            actual = leray(nonlinear(ours))
            _, expected = original_projection(original_convolution(theirs))
            self.assertEqual(set(actual), set(expected))
            for k, vector in actual.items():
                self.assertEqual(
                    [(z.real, z.imag) for z in vector],
                    [(z.real, z.imag) for z in expected[k]],
                )

    def test_exact_initial_truncation_residual(self) -> None:
        for n, phase in ROOTS:
            field = source_modes(n, phase)
            for grid in GRID_SIZES:
                decomp = exact_decomposition(field, cutoff(grid))
                self.assertEqual(decomp["kinetic_energy"], Q(2))
                self.assertEqual(decomp["dissipation"], Q(31, 2)*n*n)
                self.assertEqual(decomp["nonlinear_energy_power"], Q(0))
                self.assertEqual(
                    decomp["energy_derivative"], -VISCOSITY*Q(31, 2)*n*n,
                )
                expected = Q(1, 34) if n == 2 and grid in (16, 24) else Q(0)
                self.assertEqual(decomp["high_residual_l2_squared"], expected)
                self.assertEqual(
                    len(decomp["high_residual"]), 2 if expected else 0,
                )
                if expected:
                    for k in ((2, 8, 0), (-2, -8, 0)):
                        self.assertEqual(
                            decomp["high_residual"][k],
                            (Gaussian(Q(2*phase, 17)),
                             Gaussian(Q(-phase, 34)), Gaussian()),
                        )

    def test_exact_energy_identity_for_perturbed_solenoidal_field(self) -> None:
        field = source_modes(1, 1)
        # Separate reality-paired divergence-free mode, distinct from the
        # original eight coefficients, tests exact finite ODE algebra.
        wave = (4, -4, 4)
        vector = (Gaussian(Q(1, 7)), Gaussian(Q(1, 7)), Gaussian())
        field[wave] = vector
        field[tuple(-j for j in wave)] = opposite(vector)
        d = exact_decomposition(field, 5, Q(3, 20))
        self.assertEqual(d["nonlinear_energy_power"], 0)
        self.assertEqual(d["energy_derivative"], -Q(3, 20)*d["dissipation"])
        self.assertGreater(d["high_residual_l2_squared"], 0)

    def test_invalid_fields_rejected(self) -> None:
        with self.assertRaises(ValueError):
            source_modes(0, 1)
        with self.assertRaises(ValueError):
            source_modes(1, 0)
        with self.assertRaises(ValueError):
            cutoff(17)
        with self.assertRaises(ValueError):
            exact_decomposition(source_modes(2, 1), 3)
        with self.assertRaises(ValueError):
            exact_decomposition(source_modes(1, 1), 5, Q(0))
        field = source_modes(1, 1)
        field[(1, 0, 0)] = (Gaussian(Q(1)), Gaussian(), Gaussian())
        with self.assertRaises(ValueError):
            validate_field(field)

    def test_manifest_and_tamper_detection(self) -> None:
        rows, manifest = generate()
        self.assertEqual(len(rows), 12)
        self.assertEqual(manifest["root_count"], 4)
        self.assertEqual(
            manifest["rows_sha256"],
            "f5cd7df385430f011419db8faf5b515747a0ad20942eb09ef20fc85d4cea3fe4",
        )
        with TemporaryDirectory() as folder:
            out = Path(folder)
            self.assertEqual(freeze(out), manifest)
            self.assertEqual(audit(out), manifest)
            source = json.loads((out / "rows.json").read_text())
            source[0]["high_residual_l2_squared"] = "1/2"
            (out / "rows.json").write_text(json.dumps(source))
            with self.assertRaises(ValueError):
                audit(out)


if __name__ == "__main__":
    unittest.main()
