"""BSAR-16F: exact rational polynomial and transfer sign controls."""

from __future__ import annotations

import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.bsar16.exact_residual import (
    GRID_SIZES, ROOTS, Q, VISCOSITY, encode, source_modes, zero_vec,
)
from experiments.bsar16.rational_enclosure import (
    TIME_END, ceil_sqrt, gradient_l1, norm_squared, polynomial_at, taylor_data,
)
from experiments.bsar16.shell_signs import (
    SHELLS, _basis, _enclosure_terms, audit, certify,
    evaluate, freeze, generate, rational_error_at,
    reference_sign_margin, shell_gradient_l1, shell_modes,
    shell_transfer, shell_trilinear_error, transfer_polynomials,
)
from scripts.bsar14_initial_triad_transfer import (
    convolution as original_convolution,
    inner_real as original_inner,
    modes as original_modes,
    pressure_projection as original_projection,
)


class TestExactGalerkinShellSigns(unittest.TestCase):
    def test_exact_time_zero_source_oracle_and_shell_support(self) -> None:
        for n, phase in ROOTS:
            native = original_modes(n, Q(1), phase)
            _, projected = original_projection(original_convolution(native))
            for grid in GRID_SIZES:
                basis = _basis(n, phase, grid)
                self.assertEqual(basis["transfers"][1][0], Q(phase*n, 4))
                self.assertEqual(basis["transfers"][4][0], Q(-phase*n))
                self.assertEqual(basis["transfers"][5][0], Q(3*phase*n, 4))
                self.assertEqual(
                    sum(basis["transfers"][s][0] for s in SHELLS), Q(0)
                )
                for shell in SHELLS:
                    source_check = -sum(
                        (original_inner(native[k], projected.get(
                            k, (native[k][0]*0, native[k][0]*0, native[k][0]*0)
                        )) for k in native if sum(x*x for x in k) == shell*n*n),
                        Q(0)
                    )
                    self.assertEqual(basis["transfers"][shell][0], source_check)
                source = basis["polynomial"][0]
                self.assertEqual(shell_gradient_l1(source, n, 1), Q(2*n))
                self.assertEqual(shell_gradient_l1(source, n, 4), Q(2*n))
                self.assertEqual(shell_gradient_l1(source, n, 5), Q(5*n))
                self.assertEqual(gradient_l1(source), Q(9*n))
                self.assertEqual(len(shell_modes(n, basis["cutoff"], 1)), 6)
                self.assertEqual(len(shell_modes(n, basis["cutoff"], 4)), 6)
                self.assertEqual(len(shell_modes(n, basis["cutoff"], 5)), 24)

    def test_exact_polynomial_matches_independent_direct_evaluation(self) -> None:
        for n, phase, grid in ((1, -1, 16), (1, 1, 32), (2, -1, 24), (2, 1, 32)):
            poly, _, _ = taylor_data(n, phase, grid)
            coefficients = transfer_polynomials(poly, n)
            for t in (Q(0), Q(1, 2000), TIME_END):
                field = polynomial_at(poly, t)
                for shell in SHELLS:
                    self.assertEqual(
                        evaluate(coefficients[shell], t),
                        shell_transfer(field, n, shell),
                    )
                    self.assertEqual(len(coefficients[shell]), 7)

    def test_rational_interval_bound_and_cubic_error_terms(self) -> None:
        for pol, time, expected in (
            ((Q(1), Q(-2), Q(3)), Q(1, 4), Q(1, 2)),
            ((Q(-1), Q(2), Q(-3)), Q(1, 4), Q(1, 2)),
            ((Q(1), Q(2), Q(3)), Q(1, 4), Q(1)),
            ((Q(1), Q(-2), Q(0)), Q(1, 2), Q(0)),
        ):
            self.assertEqual(reference_sign_margin(pol, time), expected)
        with self.assertRaises(ValueError):
            reference_sign_margin((Q(0), Q(1)), TIME_END)
        with self.assertRaises(ValueError):
            evaluate((Q(1),), Q(-1, 100))
        # Keep the e² and e³ pieces in the exact trilinear expansion.
        e, p, gs, cs = Q(1, 100), Q(2), Q(3), Q(5)
        expected = (
            e*(cs*p*p+2*gs*p)
            + e*e*(2*cs*p+gs)
            + cs*e**3
        )
        self.assertEqual(shell_trilinear_error(e, p, gs, cs), expected)
        self.assertGreater(expected, e*(cs*p*p+2*gs*p))
        with self.assertRaises(ValueError):
            shell_trilinear_error(Q(-1), p, gs, cs)

    def test_positive_rational_duration_and_rigorous_gap(self) -> None:
        cases, manifest = generate()
        self.assertEqual(len(cases), len(ROOTS)*len(GRID_SIZES))
        self.assertEqual(manifest["case_count"], 12)
        self.assertEqual(manifest["shell_certificate_count"], 36)
        for case in cases:
            n, phase, grid = (
                case["frequency_N"], case["phase_sigma"], case["grid_M"]
            )
            self.assertIn((n, phase), ROOTS)
            self.assertIn(grid, GRID_SIZES)
            self.assertEqual(len(case["shells"]), 3)
            basis = _basis(n, phase, grid)
            for shell in case["shells"]:
                s = shell["shell_normalized"]
                duration = Q(shell["certified_duration"])
                self.assertGreater(duration, 0)
                self.assertLessEqual(duration, TIME_END)
                margin, ref, err, y, cs, count = _enclosure_terms(
                    basis, n, s, duration
                )
                self.assertGreater(margin, 0)
                self.assertEqual(
                    Q(shell["initial_transfer"]), basis["transfers"][s][0]
                )
                self.assertEqual(
                    shell["exact_transfer_polynomial_coefficients"],
                    [encode(x) for x in basis["transfers"][s]]
                )
                self.assertEqual(shell["shell_lattice_mode_count"], count)
                self.assertGreaterEqual(Q(shell["shell_gradient_error_constant_upper"]), cs)
                self.assertLessEqual(Q(shell["final_signed_transfer_lower"]), margin)
                self.assertGreater(Q(shell["final_signed_transfer_lower"]), 0)
                self.assertLessEqual(
                    Q(shell["reference_signed_transfer_lower"]), ref
                )
                self.assertGreaterEqual(
                    Q(shell["galerkin_transfer_difference_upper"]), err
                )
                self.assertEqual(shell["full_registered_T_certified"], duration==TIME_END)
        self.assertEqual(
            manifest["full_window_sign_cases"],
            sum(case["all_shell_signs_certified_through_T"] for case in cases)
        )

    def test_strict_sign_gate_and_regression_corruption(self) -> None:
        basis = _basis(1, 1, 16)
        result = certify(1, 1, 16)
        self.assertEqual(len(result["shells"]), 3)
        # A negative initial margin must fail even when the computed
        # reference polynomial remains nonnegative at some sample times.
        self.assertLessEqual(
            reference_sign_margin((Q(1), Q(-1)), Q(1)), Q(0)
        )
        with self.assertRaises(ValueError):
            rational_error_at(TIME_END+Q(1, 1000),
                              basis["g"], basis["d"], basis["exp_n"])
        with self.assertRaises(ValueError):
            shell_modes(0, 5, 1)

    def test_frozen_archive_integrity_and_negative_mutation(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            saved = freeze(root)
            self.assertEqual(audit(root), saved)
            rows = json.loads((root/"rows.json").read_text())
            rows[0]["shells"][0]["final_signed_transfer_lower"] = "0/1"
            (root/"rows.json").write_text(json.dumps(rows))
            with self.assertRaises(ValueError):
                audit(root)


if __name__ == "__main__":
    unittest.main()
