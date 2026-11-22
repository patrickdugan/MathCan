"""BSAR-11 exact helical Sobolev scaling and time-cutoff regressions."""

import json
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path

from scripts.bsar11_sobolev_critical_audit import (
    BASES,
    EXPONENT_QUARTERS,
    HORIZONS,
    VISCOSITIES,
    audit,
    exact_envelopes,
    family_parameters,
    generate,
    scaled_fourier,
)


class TestBSAR11SobolevScaling(unittest.TestCase):
    def test_exact_fourier_residual_and_fractional_sobolev_norm(self):
        for m in (2, 3, 4, 8, 16, 64, 128):
            for q in EXPONENT_QUARTERS:
                receipt = scaled_fourier(m, q)
                n, a, s = family_parameters(m, q)
                self.assertEqual(receipt["initial_homogeneous_Hs_seminorm_squared"], "1/1")
                self.assertEqual(receipt["regularity_s"], f"{s.numerator}/{s.denominator}")
                self.assertEqual(Q(receipt["initial_L2_norm_squared"]), a*a)
                self.assertEqual(Q(receipt["initial_enstrophy_density"]), a*a*n*n)
                self.assertTrue(receipt["mean_zero"])
                self.assertTrue(receipt["divergence_zero"])
                self.assertTrue(receipt["nonlinear_advection_zero"])
                self.assertTrue(receipt["S2_harmonic_map_tension_zero"])
                self.assertEqual(Q(receipt["direction_gradient_norm_squared"]), Q(n*n))
                self.assertEqual(receipt["pointwise_velocity_norm_squared"],
                                 f"{a.numerator*a.numerator}/{a.denominator*a.denominator}")

    def test_frequency_and_amplitude_formulae(self):
        for m in BASES:
            for q in EXPONENT_QUARTERS:
                n, a, s = family_parameters(m, q)
                self.assertEqual(n, m**4)
                self.assertEqual(a, Q(1, m**q))
                self.assertEqual(s, Q(q, 4))
                profile = scaled_fourier(m, q)
                self.assertEqual(
                    Q(profile["initial_homogeneous_Hs_seminorm_squared"]), Q(1)
                )
                self.assertEqual(Q(profile["initial_kinetic_energy_density"]), a*a/2)

    def test_analytic_cost_bound_exact_rational_receipts(self):
        for m in (2, 4, 16, 128):
            for q in EXPONENT_QUARTERS:
                for nu in VISCOSITIES:
                    for t in HORIZONS:
                        row = exact_envelopes(m, q, nu, t)
                        scale = Q(1, m**(2*q)) * m**4
                        x = Q(2) * nu * m**8 * t
                        self.assertEqual(Q(row["frequency_amplitude_scale"]), scale)
                        self.assertEqual(Q(row["x_2nuN2T"]), x)
                        self.assertEqual(
                            Q(row["initial_cone_integral_lower_rational"]),
                            scale/(2*nu) * x/(1+x),
                        )
                        self.assertEqual(
                            Q(row["initial_cone_integral_upper_rational"]),
                            scale/nu,
                        )
                        self.assertTrue(row["if_gate_J_ge_scale_over_4nu"])
                        self.assertEqual(row["Kxi_lower"], m**4)
                        self.assertEqual(row["Kxi_upper"], 2*m**4)

    def test_sharp_frequency_threshold_with_fixed_homogeneous_sobolev_norm(self):
        nu = Q(1, 100)
        t = Q(1)
        samples = [2, 4, 8, 16, 32]
        for q in EXPONENT_QUARTERS:
            lower = [Q(exact_envelopes(m, q, nu, t)[
                "initial_cone_integral_lower_rational"]) for m in samples]
            upper = [Q(exact_envelopes(m, q, nu, t)[
                "initial_cone_integral_upper_rational"]) for m in samples]
            self.assertEqual(
                [Q(exact_envelopes(m,q,nu,t)["frequency_amplitude_scale"])
                 for m in samples],
                [Q(m**(4-2*q)) if q<=2 else Q(1,m**(2*q-4)) for m in samples],
            )
            if q < 2:
                self.assertTrue(all(a<b for a,b in zip(lower, lower[1:])))
                self.assertGreater(lower[-1], lower[0]*20)
            elif q == 2:
                self.assertEqual(upper, [Q(100)] * len(samples))
                self.assertTrue(all(x>=Q(25) for x in lower))
            else:
                self.assertTrue(all(a>b for a,b in zip(upper, upper[1:])))

    def test_positive_start_time_uniform_bound_and_high_frequency_decay(self):
        nu = Q(1, 100)
        positive_start = Q(1, 100)
        t = Q(1)
        for q in EXPONENT_QUARTERS:
            tail = [Q(exact_envelopes(m,q,nu,t,positive_start)[
                "positive_start_cone_integral_upper_rational"])
                for m in (2,3,4,8,16,32,64,128)]
            self.assertTrue(all(a>b for a,b in zip(tail,tail[1:])))
            self.assertLess(tail[-1], tail[0]/100)
            self.assertTrue(all(x <= Q(1)/(2*nu*nu*positive_start) for x in tail))
        self.assertTrue(
            Q(exact_envelopes(128, 0, nu, t, positive_start)[
                "initial_cone_integral_lower_rational"])
            > Q(100000)
        )

    def test_zero_and_negative_parameters_rejected(self):
        for m,q in ((1,0),(0,2),(-1,1),(2,-1),(2,5)):
            with self.assertRaisesRegex(ValueError, "Expected"):
                family_parameters(m,q)
        for nu,t,t0 in ((Q(0),Q(1),Q(1,2)),
                        (Q(1),Q(0),Q(1,2)),
                        (Q(1),Q(1),Q(0)),
                        (Q(1),Q(1),Q(1))):
            with self.assertRaises(ValueError):
                exact_envelopes(2,0,nu,t,t0)

    def test_archive_counts_digest_and_custody(self):
        rows, receipt = generate()
        self.assertEqual(len(rows),360)
        self.assertEqual(receipt["cases"],360)
        self.assertEqual(set(x["regularity_quarters"] for x in rows),set(EXPONENT_QUARTERS))
        self.assertEqual(len({(x["base"],x["regularity_quarters"]) for x in rows}),60)
        self.assertEqual(rows,generate()[0])
        self.assertEqual(receipt,generate()[1])
        with tempfile.TemporaryDirectory() as root:
            path = Path(root)
            (path/"cases.jsonl").write_text(
                "".join(json.dumps(r,sort_keys=True)+"\n" for r in rows),
                encoding="utf-8")
            (path/"manifest.json").write_text(json.dumps(receipt),encoding="utf-8")
            self.assertEqual(audit(path),receipt)
            altered = [dict(x) for x in rows]
            altered[0]["frequency_amplitude_scale"]="0/1"
            (path/"cases.jsonl").write_text(
                "".join(json.dumps(r,sort_keys=True)+"\n" for r in altered),
                encoding="utf-8")
            with self.assertRaisesRegex(ValueError,"altered"):
                audit(path)


if __name__ == "__main__":
    unittest.main()
