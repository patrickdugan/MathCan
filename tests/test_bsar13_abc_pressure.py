"""BSAR-13: ABC Beltrami Fourier pressure balance and cone-cost controls."""

import json
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path

from scripts.bsar13_abc_pressure import (
    BASES,
    EXPONENT_QUARTERS,
    VISCOSITIES,
    HORIZONS,
    abc_modes,
    audit,
    cone_receipt,
    fourier_certificate,
    generate,
)
from scripts.bsar11_sobolev_critical_audit import family_parameters


class TestABCPressure(unittest.TestCase):
    def test_exact_six_mode_divergence_curl_pressure_and_active_advection(self):
        for m in (2, 3, 4, 8, 16, 32, 128):
            for q in EXPONENT_QUARTERS:
                receipt = fourier_certificate(m,q)
                n,a,_=family_parameters(m,q)
                self.assertTrue(receipt["six_fourier_modes"])
                self.assertTrue(receipt["divergence_zero"])
                self.assertTrue(receipt["nonlinear_advection_nonzero"])
                self.assertTrue(receipt["nonlinear_pressure_exact_cancellation"])
                self.assertEqual(receipt["curl_eigenvalue"],n)
                self.assertEqual(receipt["laplacian_eigenvalue"],-n*n)
                self.assertEqual(Q(receipt["mean_L2_squared_initial"]),3*a*a)
                self.assertEqual(Q(receipt["mean_enstrophy_initial"]),3*a*a*n*n)
                self.assertEqual(Q(receipt["mean_homogeneous_Hs_squared_initial"]),Q(3))
                self.assertEqual(
                    [Q(x) for x in receipt["advection_at_origin"]],
                    [a*a*n]*3,
                )
                self.assertEqual(
                    [Q(x) for x in receipt["pressure_gradient_at_origin"]],
                    [-a*a*n]*3,
                )
                self.assertTrue(receipt["sign_reversal_at_pi_over_n_translation"])

    def test_exact_fourier_six_modes_and_no_zero_mode(self):
        for n in (1,2,7,31):
            x=abc_modes(n,Q(1,8))
            self.assertEqual(len(x),6)
            self.assertNotIn((0,0,0),x)
            self.assertEqual({k for k in x}, {
                (n,0,0),(-n,0,0),(0,n,0),(0,-n,0),(0,0,n),(0,0,-n)
            })

    def test_cone_cost_exact_rational_envelope_all_regimes(self):
        for m in (2,4,8,16,128):
            for q in EXPONENT_QUARTERS:
                for nu in VISCOSITIES:
                    for t in HORIZONS:
                        p=cone_receipt(m,q,nu,t)
                        n,a,_=family_parameters(m,q)
                        scale=a*a*n
                        x=2*nu*n*n*t
                        self.assertTrue(p["high_core_anchor_is_half_peak"])
                        self.assertTrue(p["high_core_antipodal_pair"])
                        self.assertEqual(Q(p["Kxi_lower_N_over_2"]), Q(n,2))
                        self.assertEqual(p["Kxi_upper_24N"], 24*n)
                        self.assertEqual(Q(p["amplitude_frequency_scale"]),scale)
                        self.assertEqual(Q(p["initial_cone_integral_lower_rational"]),
                                         Q(3,4)*scale/nu *x/(1+x))
                        self.assertEqual(Q(p["initial_cone_integral_upper_rational"]),
                                         Q(36)*scale/nu)
                        self.assertTrue(p["if_gate_cone_ge_3scale_over_8nu"])

    def test_critical_H_half_threshold_with_active_pressure_advection(self):
        nu,t=Q(1,100),Q(1)
        for q in EXPONENT_QUARTERS:
            scales=[Q(cone_receipt(m,q,nu,t)["amplitude_frequency_scale"])
                    for m in (2,4,8,16,64)]
            upper=[Q(cone_receipt(m,q,nu,t)["initial_cone_integral_upper_rational"])
                   for m in (2,4,8,16,64)]
            lower=[Q(cone_receipt(m,q,nu,t)["initial_cone_integral_lower_rational"])
                   for m in (2,4,8,16,64)]
            if q<2:
                self.assertTrue(all(a<b for a,b in zip(scales,scales[1:])))
                self.assertTrue(all(a<b for a,b in zip(lower,lower[1:])))
            elif q==2:
                self.assertEqual(scales,[Q(1)]*5)
                self.assertEqual(upper,[Q(3600)]*5)
            else:
                self.assertTrue(all(a>b for a,b in zip(scales,scales[1:])))
                self.assertTrue(all(a>b for a,b in zip(upper,upper[1:])))

    def test_positive_time_high_frequency_decay(self):
        nu,t,start=Q(1,100),Q(1),Q(1,100)
        for q in EXPONENT_QUARTERS:
            upper=[Q(cone_receipt(m,q,nu,t,start)["positive_start_cone_upper_rational"])
                   for m in (4,8,16,32,64,128)]
            self.assertTrue(all(x>y for x,y in zip(upper,upper[1:])))
            self.assertTrue(all(x<=Q(18)/(nu*nu*start) for x in upper))
            self.assertLess(upper[-1],upper[0]/100)

    def test_corpus_provenance_and_tampering(self):
        rows,receipt=generate()
        self.assertEqual(len(rows),360)
        self.assertEqual(receipt["cases"],360)
        self.assertEqual(receipt["Hs_squared_initial"],"3/1")
        self.assertEqual(receipt["nonlinear_advection_zero"],False)
        self.assertEqual(receipt["source_commits"]["bsar12"],
                         "0faa26a99c3e4a69540a429ed12901ea69bc063b")
        self.assertEqual(rows,generate()[0])
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)
            (path/"cases.jsonl").write_text(
                "".join(json.dumps(x,sort_keys=True)+"\n" for x in rows),encoding="utf-8"
            )
            (path/"manifest.json").write_text(json.dumps(receipt),encoding="utf-8")
            self.assertEqual(audit(path),receipt)
            tampered=[dict(x) for x in rows]
            tampered[0]["initial_cone_integral_lower_rational"]="0/1"
            (path/"cases.jsonl").write_text(
                "".join(json.dumps(x,sort_keys=True)+"\n" for x in tampered),encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError,"modified"):
                audit(path)

    def test_invalid_values_rejected(self):
        for n,a in ((0,Q(1)),(1,Q(0)),(1,Q(-1))):
            with self.assertRaises(ValueError):
                abc_modes(n,a)
        for nu,t,start in (
            (Q(0),Q(1),Q(1,2)),
            (Q(1),Q(0),Q(1,2)),
            (Q(1),Q(1),Q(0)),
            (Q(1),Q(1),Q(1)),
        ):
            with self.assertRaises(ValueError):
                cone_receipt(2,0,nu,t,start)


if __name__=="__main__":
    unittest.main()
