"""BSAR-16C rational interval vorticity-core anchor controls."""

from __future__ import annotations

import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.bsar16.exact_residual import GRID_SIZES, ROOTS, Q
from experiments.bsar16.core_intervals import (
    PI_UPPER,
    anchor_certificate_from_epsilon,
    audit,
    certify,
    floor_sqrt,
    freeze,
    generate,
    round_down,
)
from experiments.bsar16.rational_enclosure import (
    ceil_sqrt, gradient_l1, taylor_data,
)
from scripts.bsar14_initial_triad_transfer import (
    exact_point as bsar14_point,
    modes as bsar14_modes,
)


class TestRationalCoreAnchors(unittest.TestCase):
    def test_exact_bsar14_anchors_and_source_gradient(self) -> None:
        for n, phase in ROOTS:
            source = bsar14_modes(n, Q(1), phase)
            a0 = bsar14_point(source, n, x_pi_over_n=False)["vorticity"]
            a1 = bsar14_point(source, n, x_pi_over_n=True)["vorticity"]
            self.assertEqual(
                tuple(x.real for x in a0), (Q(0), -Q(n), -Q(5*phase*n))
            )
            self.assertEqual(
                tuple(x.real for x in a1), (Q(0), -Q(n), Q(5*phase*n))
            )
            for grid in GRID_SIZES:
                polynomial, _, _ = taylor_data(n, phase, grid)
                self.assertEqual(gradient_l1(polynomial[0]), Q(9*n))

    def test_directed_square_root_and_anchor_inequalities(self) -> None:
        for q in (Q(0), Q(26), Q(65), Q(50, 13), Q(123, 7)):
            self.assertLessEqual(floor_sqrt(q)**2, q)
            self.assertGreaterEqual(ceil_sqrt(q)**2, q)
        self.assertEqual(round_down(Q(1, 10)), Q(1, 10))
        self.assertEqual(PI_UPPER, Q(22, 7))
        at_zero = anchor_certificate_from_epsilon(1, Q(0))
        self.assertTrue(at_zero["positive_cone_witness_certified"])
        self.assertGreater(
            Q(at_zero["cone_Kxi_anchor_lower"]), Q(1)
        )
        eps1 = anchor_certificate_from_epsilon(1, Q(1, 4))
        eps2 = anchor_certificate_from_epsilon(1, Q(1, 2))
        self.assertTrue(eps1["core_pair_certified"])
        self.assertTrue(eps2["core_pair_certified"])
        self.assertGreater(
            Q(eps1["cone_Kxi_anchor_lower"]),
            Q(eps2["cone_Kxi_anchor_lower"]),
        )

    def test_all_twelve_galerkin_core_pairs_have_positive_margins(self) -> None:
        rows, manifest = generate()
        self.assertEqual(len(rows), len(ROOTS)*len(GRID_SIZES))
        self.assertEqual(manifest["cases"], 12)
        self.assertEqual(manifest["certified_core_pairs"], 12)
        self.assertEqual(manifest["positive_cone_witnesses"], 12)
        for row in rows:
            n = row["frequency_N"]
            self.assertTrue(row["core_pair_certified"])
            self.assertTrue(row["positive_cone_witness_certified"])
            self.assertEqual(row["source_gradient_fourier_l1"], f"{9*n}/1")
            self.assertEqual(
                row["initial_normalized_direction_difference_squared"],
                "50/13",
            )
            self.assertGreater(
                Q(row["half_maximum_core_margin_lower"]), Q(0)
            )
            self.assertGreater(
                Q(row["galerkin_anchor_vorticity_norm_lower"])*2,
                Q(row["galerkin_global_vorticity_sup_upper"]),
            )
            self.assertGreater(
                Q(row["normalized_direction_separation_lower"]), Q(0)
            )
            self.assertGreater(
                Q(row["cone_Kxi_anchor_lower"]), Q(0)
            )
            self.assertIn("not a float", row["scope"])
        # Conservative negative controls expose the exact acceptance gate:
        fail = anchor_certificate_from_epsilon(2, Q(3))
        self.assertFalse(fail["core_pair_certified"])
        self.assertIsNone(fail["cone_Kxi_anchor_lower"])

    def test_invalid_requests_are_rejected(self) -> None:
        for n, epsilon in ((0, Q(0)), (1, Q(-1, 2))):
            with self.assertRaises(ValueError):
                anchor_certificate_from_epsilon(n, epsilon)
        with self.assertRaises(ValueError):
            floor_sqrt(Q(-1))
        with self.assertRaises(ValueError):
            round_down(Q(-1))

    def test_archive_reproducible_and_tamper_detected(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            saved = freeze(root)
            self.assertEqual(audit(root), saved)
            rows = json.loads((root/"rows.json").read_text())
            rows[0]["core_pair_certified"] = False
            (root/"rows.json").write_text(json.dumps(rows))
            with self.assertRaises(ValueError):
                audit(root)


if __name__ == "__main__":
    unittest.main()
