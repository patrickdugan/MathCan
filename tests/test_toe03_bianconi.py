"""TOE-03 reproducible checks; every numerical input is synthetic."""
import random
import unittest
from fractions import Fraction as F
from research.toe.bianconi_profile import (
    check_spd, det, dot, dynamic_template, frw_background, frw_design,
    injection_case, profile, profile_template, proxy_expansion_hubble,
    proxy_expansion_squared, rational, redshift_grid, reference_experiment,
    schur_information, solve, synthetic_covariance, gfield_mode, gfield_entropy_series,
)


Z = tuple(F(i, 5) for i in range(7))
BASE = (F(17, 25), F(0), F(8, 25), F(0))


class BianconiProxyTests(unittest.TestCase):
    def test_exact_solver(self):
        self.assertEqual(solve(((2,1),(1,3)),(5,7)), (F(8,5), F(9,5)))
        self.assertEqual(det(((2,1),(1,3))),5)
        self.assertEqual(det(((1,1),(1,1))),0)

    def test_fractional_redshifts_and_normalization(self):
        self.assertEqual(frw_design((0,F(1,2)))[1],(1,F(9,4),F(27,8),F(81,16)))
        self.assertEqual(proxy_expansion_squared((0,),BASE,F(1,100),5),(1,))
        self.assertEqual(dynamic_template((0,F(1,5)),5)[0],0)
        self.assertGreater(proxy_expansion_hubble((0,1),BASE,0,5,70)[1],70)

    def test_design_rank_degeneracies(self):
        c=synthetic_covariance(Z)
        for p in (0,2,3,4):
            self.assertEqual(profile_template(Z,c,p)["chi2"],0)
        for p in (1,5,6):
            self.assertGreater(profile_template(Z,c,p)["chi2"],0)

    def test_schur_determinant_agrees_with_profile(self):
        c=synthetic_covariance(Z)
        for p in (0,1,2,3,4,5,6):
            self.assertEqual(schur_information(Z,c,p),profile_template(Z,c,p)["chi2"])

    def test_exact_injected_amplitude_law(self):
        c=synthetic_covariance(Z)
        for e in (F(0),F(1,1000),F(-1,1000),F(1,100)):
            row=injection_case(Z,c,BASE,e,5)
            self.assertEqual(row["chi2"],e*e*row["fisher"])
            self.assertGreaterEqual(row["chi2"],0)

    def test_calibration_noise_in_nuisance_span_invisible(self):
        base=synthetic_covariance(Z,calibration=0)
        for mode in ("constant","curvature"):
            for tau in (0,F(1,40),F(7,20)):
                new=synthetic_covariance(Z,calibration=tau,mode=mode)
                for p in (1,5):
                    self.assertEqual(profile_template(Z,base,p)["chi2"],
                                     profile_template(Z,new,p)["chi2"])

    def test_correlations_change_profile_information(self):
        corr=synthetic_covariance(Z,rho=F(1,2),calibration=0)
        diag=synthetic_covariance(Z,rho=0,calibration=0)
        self.assertNotEqual(profile_template(Z,corr,5)["chi2"],
                            profile_template(Z,diag,5)["chi2"])

    def test_exact_profile_gauge_analogy(self):
        c=synthetic_covariance(Z)
        base=frw_background(Z,BASE)
        f=dynamic_template(Z,5)
        offset=frw_background(Z,(5,-2,3,1))
        y=tuple(a+b for a,b in zip(base,f))
        yoffset=tuple(a+b for a,b in zip(y,offset))
        self.assertEqual(profile(y,frw_design(Z),c)["chi2"],
                         profile(yoffset,frw_design(Z),c)["chi2"])

    def test_covariance_spd_and_bad_inputs(self):
        self.assertEqual(check_spd(((F(1),F(1,2)),(F(1,2),F(1))))[0][0],1)
        for bad in (((1,2),(2,1)),((1,2),(0,1)),((0,0),(0,1))):
            with self.assertRaises(ValueError):check_spd(bad)
        with self.assertRaises(ValueError):synthetic_covariance(Z,rho=1)
        with self.assertRaises(ValueError):synthetic_covariance(Z,calibration=-1)
        with self.assertRaises(ValueError):synthetic_covariance(Z,mode="other")

    def test_rank_deficient_and_repeated_redshifts(self):
        with self.assertRaises(ValueError):redshift_grid([0,0])
        with self.assertRaises(ValueError):redshift_grid([F(-1,2)])
        with self.assertRaises(ValueError):profile_template([0,1,2],((1,0,0),(0,1,0),(0,0,1)),5)
        with self.assertRaises(ValueError):profile_template([0,0,1,2,3],
                                                        tuple(tuple(int(i==j) for j in range(5)) for i in range(5)),5)

    def test_proxy_positivity_and_no_float_inputs(self):
        with self.assertRaises(ValueError):proxy_expansion_squared((0,1),BASE,F(-10),5)
        with self.assertRaises(TypeError):rational(0.5)
        with self.assertRaises(ValueError):dynamic_template(Z,-1)
        with self.assertRaises(ValueError):proxy_expansion_hubble((0,),BASE,0,5,0)

    def test_gfield_second_order_blind_mode(self):
        c=synthetic_covariance(Z)
        # A G-field component G=1+g*(x^2-1) produces g^2/2*(x^2-1)^2
        # at quadratic order in G-1. This lies in span{1,x^2,x^4}.
        self.assertEqual(profile(gfield_mode(Z,power=2,order=2),frw_design(Z),c)["chi2"],0)
        self.assertGreater(profile(gfield_mode(Z,power=2,order=3),frw_design(Z),c)["chi2"],0)
        self.assertGreater(profile(gfield_mode(Z,power=1,order=2),frw_design(Z),c)["chi2"],0)

    def test_gfield_entropy_alternating_brackets(self):
        # Alternating tail bound for 0<=u<1; odd and even partials bracket.
        p3=gfield_entropy_series(Z,F(1,100),power=2,cutoff=3)
        p4=gfield_entropy_series(Z,F(1,100),power=2,cutoff=4)
        p8=gfield_entropy_series(Z,F(1,100),power=2,cutoff=8)
        for (lo,_),(hi,_),(mid,err) in zip(p3,p4,p8):
            self.assertLessEqual(lo,mid)
            self.assertLessEqual(mid,hi)
            self.assertLessEqual(err,F(1,9))
        with self.assertRaises(ValueError):gfield_entropy_series(Z,1,power=2)

    def test_machine_readable_receipt(self):
        r=reference_experiment()
        self.assertEqual(r["data_status"],"synthetic illustrative E^2; no observational constraint")
        self.assertEqual(r["projections"]["p2"],"0")
        self.assertEqual(r["projections"]["p3"],"0")
        self.assertEqual(r["projections"]["p4"],"0")
        self.assertEqual(len(r["covariance_E2"]),7)
        self.assertGreater(r["unit_amplitude_sigma"],0)
        self.assertLess(r["synthetic_snr"],1)

    def test_random_exact_covariances(self):
        rng=random.Random(20261111)
        for _ in range(12):
            z=tuple(F(i,rng.randint(4,9)) for i in range(6))
            if len(set(z))!=len(z):continue
            c=synthetic_covariance(z,rho=F(rng.randint(0,3),4),
                                   calibration=F(rng.randint(0,3),10))
            self.assertEqual(schur_information(z,c,5),
                             profile_template(z,c,5)["chi2"])


if __name__ == "__main__":
    unittest.main()
