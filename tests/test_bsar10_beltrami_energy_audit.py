"""BSAR-10 exact Fourier periodic NSE and rational lower-bound tests."""

import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from scripts.bsar10_beltrami_energy_audit import (
    FREQUENCIES,
    HORIZONS,
    VISCOSITIES,
    G,
    check_fourier,
    exact_lower_receipt,
    generate,
    validate,
)

Q = Fraction


class TestBSAR10Beltrami(unittest.TestCase):
    def test_exact_gaussian_rational_arithmetic(self):
        i = G(Q(0), Q(1))
        self.assertEqual(i * i, G(Q(-1)))
        self.assertEqual((G(Q(1, 2)) + i * Q(1, 2)).magnitude_squared(), Q(1, 2))

    def test_exact_fourier_pde_and_vorticity_identities(self):
        for n in (1, 2, 3, 7, 16, 31, 256, 2048):
            data = check_fourier(n)
            self.assertTrue(data["mean_zero"])
            self.assertTrue(data["divergence_zero"])
            self.assertTrue(data["nonlinear_advection_zero"])
            self.assertEqual(data["profile_pointwise_norm_squared"], "1/1")
            self.assertEqual(data["profile_pointwise_gradient_squared"], str(n * n))
            self.assertTrue(data["direction_harmonic_map_tension_zero"])
            self.assertEqual(data["curl_eigenvalue"], -n)
            self.assertEqual(data["laplacian_eigenvalue"], -(n * n))
            self.assertEqual(data["pressure"], "0")
            self.assertEqual(data["velocity_norm_sq_spatial_average_t0"], "1/1")
            self.assertEqual(data["vorticity_norm_sq_spatial_average_t0"], str(n * n))

    def test_exact_rational_dissipation_and_cone_cost_lower_bound(self):
        for n in FREQUENCIES:
            for nu in VISCOSITIES:
                for horizon in HORIZONS:
                    receipt = exact_lower_receipt(n, nu, horizon)
                    self.assertEqual(receipt["initial_kinetic_energy_density"], "1/2")
                    self.assertEqual(receipt["viscous_dissipation_upper"], "1/2")
                    self.assertEqual(receipt["direction_seminorm_lower"], f"{n}/1")
                    x = 2 * nu * n * n * horizon
                    self.assertEqual(Q(receipt["x_equals_2nu_n2_T"]), x)
                    exact_rational_lower = Q(n, 1) / (2 * nu) * x / (1 + x)
                    self.assertEqual(
                        Q(receipt["integrated_Kxi_D_lower_rational"]),
                        exact_rational_lower,
                    )
                    self.assertTrue(
                        receipt["if_gate_then_integrated_Kxi_D_ge_n_over_4nu"]
                    )
                    if x >= 1:
                        self.assertGreaterEqual(exact_rational_lower, Q(n, 1) / (4 * nu))

    def test_fixed_initial_energy_and_unbounded_frequency_floor(self):
        nu, horizon = Q(1, 100), Q(1)
        points = [
            exact_lower_receipt(n, nu, horizon)
            for n in (8, 16, 32, 64, 128, 512, 2048)
        ]
        floors = [Q(x["integrated_Kxi_D_lower_rational"]) for x in points]
        self.assertEqual({x["initial_kinetic_energy_density"] for x in points}, {"1/2"})
        self.assertTrue(all(a < b for a, b in zip(floors, floors[1:])))
        self.assertGreater(floors[-1], 200 * floors[0])
        self.assertTrue(all(x["high_frequency_gate_2nu_n2_T_ge_1"] for x in points))

    def test_corpus_is_stable_and_checks_modifications(self):
        rows, manifest = generate()
        self.assertEqual(manifest["cases"], len(FREQUENCIES) * len(VISCOSITIES) * len(HORIZONS))
        self.assertEqual(len(rows), 414)
        self.assertEqual(manifest["source_commit"], "80c62433b0eb671175bd8d6169822d3ebd922b60")
        validate(rows, manifest)
        again, repeat = generate()
        self.assertEqual(rows, again)
        self.assertEqual(manifest, repeat)
        tampered = [dict(r) for r in rows]
        tampered[0]["integrated_Kxi_D_lower_rational"] = "0/1"
        with self.assertRaisesRegex(ValueError, "Altered"):
            validate(tampered, manifest)
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "cases.jsonl").write_text(
                "".join(json.dumps(r, sort_keys=True) + "\n" for r in rows)
            )
            assert (root / "cases.jsonl").read_text()

    def test_invalid_domain_and_zero_viscosity_rejected(self):
        for n in (0, -1):
            with self.assertRaisesRegex(ValueError, "positive"):
                check_fourier(n)
        for n, nu, horizon in (
            (0, Q(1), Q(1)),
            (1, Q(0), Q(1)),
            (1, Q(-1), Q(1)),
            (1, Q(1), Q(0)),
        ):
            with self.assertRaisesRegex(ValueError, "Expected"):
                exact_lower_receipt(n, nu, horizon)


if __name__ == "__main__":
    unittest.main()
