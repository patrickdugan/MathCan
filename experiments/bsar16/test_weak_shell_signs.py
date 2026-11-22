"""BSAR-16H: audit a.e.-in-time Leray--Hopf shell-sign evidence."""

from __future__ import annotations

import json
import unittest
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from experiments.bsar16.exact_residual import (
    GRID_SIZES, ROOTS, Q, source_modes, VISCOSITY,
)
from experiments.bsar16.conditional_nse_shells import generate as source_generate
from experiments.bsar16.rational_enclosure import exp_upper
from experiments.bsar16.shell_signs import SHELLS
from experiments.bsar16.weak_shell_signs import (
    HORIZON,
    MEASURABLE_TIME_SCOPE,
    SOURCE_BSAR16G_ROWS_SHA256,
    audit,
    exact_residual_sign_audit,
    freeze,
    generate,
    gradient_squared,
    pairing,
)


class TestWeakRelativeEnergyAlgebra(unittest.TestCase):
    def test_forced_comparison_sign_and_viscous_coefficient(self) -> None:
        receipt = exact_residual_sign_audit(2, 1, 16)
        self.assertEqual(receipt["relative_energy_left"],
                         receipt["relative_energy_right"])
        self.assertEqual(receipt["transport_cancellation"], "0/1")
        self.assertGreater(Q(receipt["high_mode_work"]), 0)
        self.assertIn("-r_K", receipt["residual_sign"])
        self.assertEqual(set(receipt["shell_transfers"]), {"1", "4", "5"})

    def test_l2_and_gradient_quadratic_scaling(self) -> None:
        from experiments.bsar16.rational_enclosure import scale_field
        field = source_modes(2, -1)
        self.assertEqual(pairing(field, field), Q(4))
        self.assertEqual(gradient_squared(field), Q(62))
        for q in (Q(1, 11), Q(-2, 3), Q(13, 5)):
            scaled = scale_field(field, q)
            self.assertEqual(pairing(scaled, scaled), 4*q*q)
            self.assertEqual(gradient_squared(scaled), 62*q*q)
        # Exact rational exp majorant used in BSAR-16B's
        # weak integral Gronwall comparison.
        self.assertEqual(exp_upper(Q(0)), Q(1))
        self.assertGreaterEqual(exp_upper(Q(1, 10)), Q(11, 10))

    def test_wrong_source_and_missing_high_mode_rejected(self) -> None:
        for n, phase, grid in ((1, -1, 16), (1, 1, 32), (2, 1, 32)):
            with self.assertRaises(ValueError):
                exact_residual_sign_audit(n, phase, grid)
        with self.assertRaises(ValueError):
            exact_residual_sign_audit(2, 7, 16)


class TestWeakCertificateCustody(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.records, cls.manifest = generate()

    def test_sealed_bsar16g_provenance_and_ae_signs(self) -> None:
        source_rows, source_manifest = source_generate()
        self.assertEqual(
            source_manifest["rows_sha256"], SOURCE_BSAR16G_ROWS_SHA256
        )
        self.assertEqual(len(source_rows), 12)
        self.assertEqual(self.manifest["cases"], 12)
        self.assertEqual(self.manifest["a.e._shell_certificates"], 36)
        self.assertEqual(self.manifest["smooth_nse_lifespan_premise"], False)
        self.assertEqual(self.manifest["time_scope"], MEASURABLE_TIME_SCOPE)
        self.assertIn("not Lean", self.manifest["mathematical_proof_scope"])
        self.assertEqual(
            self.manifest["source_bsar16g_rows_sha256"],
            SOURCE_BSAR16G_ROWS_SHA256
        )
        self.assertEqual(
            {(r["frequency_N"], r["phase_sigma"], r["grid_M"])
             for r in self.records},
            {(n, phase, grid) for n, phase in ROOTS for grid in GRID_SIZES}
        )
        for record in self.records:
            n, phase = record["frequency_N"], record["phase_sigma"]
            self.assertEqual(record["time_horizon"], "3/250")
            self.assertEqual(record["valid_times"], MEASURABLE_TIME_SCOPE)
            self.assertFalse(record["full_smooth_nse_existence_premise"])
            self.assertTrue(record["requires_leray_hopf_weak_form_and_energy_inequality"])
            self.assertIn("every periodic", record["valid_for"])
            self.assertEqual(len(record["source_shells"]), 3)
            for row in record["source_shells"]:
                shell = row["shell_normalized"]
                self.assertIn(shell, SHELLS)
                expected = {1: Q(phase*n, 4),
                            4: Q(-phase*n),
                            5: Q(3*phase*n, 4)}
                self.assertEqual(Q(row["original_signed_transfer"]), expected[shell])
                self.assertEqual(row["certified_ae_duration"], "3/250")
                self.assertGreater(Q(row["leray_hopf_ae_signed_transfer_lower"]), 0)
                self.assertGreaterEqual(
                    Q(row["weak_solution_L2_to_reference_upper"]), 0
                )
                self.assertIn("almost every", row["time_quantifier"])
                self.assertIn("relative-energy", row["source_strong_hypothesis_discharge"])

    def test_wrong_input_sha_and_negative_archive_mutation(self) -> None:
        with patch("experiments.bsar16.weak_shell_signs.source_generate",
                   return_value=([], {"rows_sha256": "wrong"})):
            with self.assertRaisesRegex(ValueError, "archive hash changed"):
                generate()
        with TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = freeze(root)
            self.assertEqual(self.manifest, manifest)
            self.assertEqual(manifest, audit(root))
            changed = json.loads((root/"rows.json").read_text(encoding="utf-8"))
            changed[0]["source_shells"][0]["leray_hopf_ae_signed_transfer_lower"] = "0/1"
            (root/"rows.json").write_text(json.dumps(changed))
            with self.assertRaises(ValueError):
                audit(root)


if __name__ == "__main__":
    unittest.main()
