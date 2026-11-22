"""BSAR-12 exact 2-mode Navier-Stokes, nonzero tension and cone scaling tests."""

import json
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path

from scripts.bsar12_two_mode_helical import (
    BASES,
    EXPONENT_QUARTERS,
    HORIZONS,
    VISCOSITIES,
    audit,
    bounds,
    exact_fourier,
    family_parameters,
    generate,
    tension_witness,
)


class TestTwoModeHelical(unittest.TestCase):
    def test_fourier_zero_advection_and_distinct_heat_decay(self):
        for m in (2, 3, 4, 12, 32, 128):
            for q in EXPONENT_QUARTERS:
                r = exact_fourier(m, q)
                n, a, _ = family_parameters(m, q)
                self.assertEqual(r["mode_count"], 4)
                self.assertTrue(r["mean_zero"])
                self.assertTrue(r["divergence_zero"])
                self.assertTrue(r["zero_nonlinear_advection"])
                self.assertTrue(r["exact_heat_mode_balance"])
                self.assertEqual(r["pressure"], "0")
                self.assertEqual(Q(r["L2_norm_squared_avg_t0"]), Q(65, 64) * a * a)
                self.assertEqual(
                    Q(r["initial_enstrophy_density"]),
                    n * n * a * a * Q(17, 16),
                )
                self.assertEqual({abs(x["k"][2]) for x in r["fourier_support"]},
                                 {n, 2*n})

    def test_tension_is_explicitly_nonzero_and_not_a_single_beltrami_eigenmode(self):
        for n in (1, 2, 8, 13, 256):
            r = tension_witness(n)
            self.assertEqual(Q(r["ratio_2B_over_A"]), Q(1, 4))
            self.assertEqual(Q(r["absolute_tension"]), Q(60, 289) * n * n)
            self.assertEqual(
                Q(r["direction_angular_acceleration_over_n_squared"]), -Q(60, 289)
            )
            self.assertTrue(r["positive_tension"])
        for ratio in (Q(1, 10), Q(1, 5), Q(1, 4)):
            r = tension_witness(2, ratio)
            self.assertGreater(Q(r["absolute_tension"]), 0)

    def test_sobolev_interval_includes_exact_irrational_weight_bound(self):
        expected = {0: Q(65, 64), 2: Q(33, 32), 4: Q(17, 16)}
        for m in BASES:
            for q in EXPONENT_QUARTERS:
                d = exact_fourier(m, q)
                lo = Q(d["initial_homogeneous_Hs_squared_lower"])
                hi = Q(d["initial_homogeneous_Hs_squared_upper"])
                self.assertTrue(Q(1) < lo <= hi <= Q(17, 16))
                self.assertEqual(d["initial_Hs_interval_exact_if_even_q"], q % 2 == 0)
                if q in expected:
                    self.assertEqual(lo, expected[q])
                    self.assertEqual(hi, expected[q])
                else:
                    self.assertLess(lo, hi)

    def test_full_torus_core_and_rational_integral_brackets(self):
        for m in (2, 4, 8, 16, 64, 128):
            for q in EXPONENT_QUARTERS:
                for nu in VISCOSITIES:
                    for t in HORIZONS:
                        r = bounds(m, q, nu, t)
                        n, a, _ = family_parameters(m, q)
                        scale = a * a * n
                        x = 2 * nu * n * n * t
                        self.assertTrue(r["all_points_above_half_peak"])
                        self.assertEqual(r["high_vorticity_core_fraction_lower"], "3/5")
                        self.assertEqual(r["cone_lower_n"], n)
                        self.assertEqual(r["cone_upper_4n"], 4 * n)
                        self.assertEqual(
                            Q(r["integrated_cone_lower_rational"]),
                            scale / (2 * nu) * x / (1 + x),
                        )
                        self.assertEqual(
                            Q(r["integrated_cone_upper_rational"]),
                            Q(17, 8) * scale / nu,
                        )
                        self.assertTrue(r["if_large_time_lower_at_least_A2N_over_4nu"])

    def test_hs_critical_frequency_threshold(self):
        nu, t = Q(1, 100), Q(1)
        bases = (2, 4, 8, 16, 64)
        for q in EXPONENT_QUARTERS:
            scale = [Q(bounds(m, q, nu, t)["cone_cost_scale_A2N"]) for m in bases]
            lower = [
                Q(bounds(m, q, nu, t)["integrated_cone_lower_rational"])
                for m in bases
            ]
            upper = [
                Q(bounds(m, q, nu, t)["integrated_cone_upper_rational"])
                for m in bases
            ]
            if q < 2:
                self.assertTrue(all(x < y for x, y in zip(scale, scale[1:])))
                self.assertTrue(all(x < y for x, y in zip(lower, lower[1:])))
            elif q == 2:
                self.assertEqual(scale, [Q(1)] * len(bases))
                self.assertEqual(upper, [Q(425, 2)] * len(bases))
            else:
                self.assertTrue(all(x > y for x, y in zip(scale, scale[1:])))
                self.assertTrue(all(x > y for x, y in zip(upper, upper[1:])))

    def test_positive_start_rational_upper_and_crossover(self):
        nu, t, start = Q(1, 100), Q(1), Q(1, 100)
        for q in EXPONENT_QUARTERS:
            upper = [
                Q(bounds(m, q, nu, t, start)["positive_start_upper_rational"])
                for m in (4, 8, 16, 32, 64, 128)
            ]
            self.assertTrue(all(x > y for x, y in zip(upper, upper[1:])))
            self.assertLess(upper[-1], upper[0] / 100)
            self.assertTrue(all(x <= Q(17, 16) / (nu * nu * start) for x in upper))
        self.assertLess(
            Q(bounds(2, 0, nu, t, start)["positive_start_upper_rational"]),
            Q(bounds(3, 0, nu, t, start)["positive_start_upper_rational"]),
        )

    def test_corpus_replay_and_tampering_rejected(self):
        rows, manifest = generate()
        self.assertEqual(len(rows), 360)
        self.assertEqual(manifest["cases"], 360)
        self.assertEqual(manifest["exact_nonzero_tension_ratio"], "60/289")
        self.assertEqual(rows, generate()[0])
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            (target / "cases.jsonl").write_text(
                "".join(json.dumps(x, sort_keys=True) + "\n" for x in rows),
                encoding="utf-8",
            )
            (target / "manifest.json").write_text(
                json.dumps(manifest, sort_keys=True), encoding="utf-8"
            )
            self.assertEqual(audit(target), manifest)
            tampered = [dict(x) for x in rows]
            tampered[0]["integrated_cone_lower_rational"] = "0/1"
            (target / "cases.jsonl").write_text(
                "".join(json.dumps(x, sort_keys=True) + "\n" for x in tampered),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "tampered"):
                audit(target)

    def test_invalid_parameters_rejected(self):
        for m, q in ((1, 0), (2, -1), (2, 5)):
            with self.assertRaises(ValueError):
                exact_fourier(m, q)
        for n, r in ((0, Q(1, 4)), (1, Q(0)), (1, Q(1, 3))):
            with self.assertRaises(ValueError):
                tension_witness(n, r)
        for nu, t, start in (
            (Q(0), Q(1), Q(1, 2)),
            (Q(1), Q(0), Q(1, 2)),
            (Q(1), Q(1), Q(0)),
            (Q(1), Q(1), Q(1)),
        ):
            with self.assertRaises(ValueError):
                bounds(2, 0, nu, t, start)


if __name__ == "__main__":
    unittest.main()
