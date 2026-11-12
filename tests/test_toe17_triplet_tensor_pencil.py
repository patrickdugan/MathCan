"""TOE-17 independent source contraction, characteristic, and D-gauge tests."""
import unittest
from fractions import Fraction as F
from random import Random

from research.toe.triplet_tensor_pencil import (
    source_responses, source_tensor_matrix, closed_entries, check_closed_pencil,
    cubic_coefficients, source_jordan_reference, detuned_reference,
    scalar_longitudinal_response, reference_experiment,
    _forms_background, _matter_oneforms, _dforms, PAIRS,
)
from research.toe.wave_principal import evaluate_polynomial
from research.toe.form_sector_principal import cubic_discriminant
from research.toe.operator_principal import wave_field_strength


class ThreeMultipletPencilTests(unittest.TestCase):
    def test_independent_sector_reference_denominators(self):
        r=source_responses()
        self.assertEqual(r['thetaE'],F(124,125))
        self.assertEqual(r['thetaB'],F(124,125))
        self.assertEqual(r['theta_s'],F(122,125))
        self.assertEqual(r['theta_t'],F(247,250))
        self.assertEqual(r['theta0'],F(229,250))
        self.assertEqual(r['We'],r['Wb'])

    def test_full_six_bivector_plus_ricci_direct_closed_form(self):
        for omega,p in ((0,1),(1,1),(-1,1),(F(1,2),2),
                        (F(5,3),F(3,4)),(2,1),(-2,3),
                        (F(),F(3)),(F(3),F())):
            report=check_closed_pencil(omega,p)
            self.assertTrue(report['SO2_closed_inside_trial'])
            self.assertEqual(report['two_helicity_det'],
                             report['one_helicity_det']**2)

    def test_helcity_pair_no_cross_and_equal_diagonals(self):
        rng=Random(1717)
        for _ in range(18):
            w=F(rng.randrange(-4,5),rng.randrange(1,5))
            p=F(rng.randrange(0,5),rng.randrange(1,5))
            m=source_tensor_matrix(w,p)
            hh,hm,mm=closed_entries(w,p)
            self.assertEqual((m[0][0],m[0][2],m[2][2]),(hh,hm,mm))
            self.assertEqual(m[0][1],0)
            self.assertEqual(m[0][3],0)
            self.assertEqual(m[1][2],0)
            self.assertEqual(m[2][3],0)
            self.assertEqual(m[1][1],hh)
            self.assertEqual(m[1][3],hm)
            self.assertEqual(m[3][3],mm)

    def test_matched_jordan_exact_coefficients(self):
        j=source_jordan_reference()
        self.assertEqual(j['head_root'],1)
        self.assertEqual(j['at_root_rank'],1)
        self.assertEqual(j['root_multiplicity'],2)
        self.assertTrue(j['regular_temporal_pencil'])
        self.assertEqual(j['jordan_v0'],(1,0))
        self.assertEqual(j['jordan_v1'],(0,F(-10,3)))
        self.assertEqual(j['extra_root'],F(1158253,1154113))
        self.assertGreater(j['extra_root'],1)

    def test_one_helicity_exact_reference_polynomial(self):
        c=cubic_coefficients()
        factor=F(75,14075583041536)
        a,b=F(1154113),F(1158253)
        for x in (-1,0,F(1,3),1,F(11,10),4):
            self.assertEqual(evaluate_polynomial(c,x),factor*(x-1)**2*(a*x-b))
        self.assertEqual(cubic_discriminant(c),0)
        self.assertEqual(evaluate_polynomial(c,1),0)

    def test_nonzero_eigenvalue_at_repeated_lightcone(self):
        hh,hm,mm=closed_entries(1)
        self.assertEqual((hh,hm,mm),(0,0,F(9,61504)))
        # The root is defective for the regular two-field polynomial
        # linearization: det multiplicity 2, polynomial matrix nullity 1.
        self.assertNotEqual(mm,0)
        bprime=2*F(15,61504)
        self.assertEqual(bprime+mm*F(-10,3),0)

    def test_source_matter_not_original_bare_yang_mills(self):
        # At p=1, omega=0, source matter Hessian remains negative;
        # the TOE-11 bare YM term is absent in the source action.
        hh,ha,aa=closed_entries(0)
        self.assertEqual(hh,F(58525,228856384))
        self.assertEqual(ha,F(-15,61504))
        self.assertEqual(aa,F(-1470,61504))

    def test_wave_homogeneity_and_frequency_polynomial(self):
        rng=Random(1718)
        for _ in range(12):
            omega=F(rng.randrange(-6,7),3)
            p=F(rng.randrange(1,6),4)
            t=F(rng.randrange(1,5),3)
            a,b,c=closed_entries(omega,p)
            at,bt,ct=closed_entries(omega*t,p*t)
            self.assertEqual(at,t**4*a)
            self.assertEqual(bt,t**3*b)
            self.assertEqual(ct,t**2*c)
            coeff=cubic_coefficients()
            self.assertEqual(a*c-b*b,p**6*evaluate_polynomial(coeff,(omega/p)**2))

    def test_detuning_positive_and_negative_three_distinct_real_x(self):
        for eps in (F(-1,1000),F(1,1000)):
            z=detuned_reference(eps)
            self.assertGreater(z['discriminant'],0)
            self.assertTrue(z['three_distinct_positive_x'])
            coeff=cubic_coefficients(lam=1+eps)
            self.assertEqual(z['discriminant'],cubic_discriminant(coeff))

    def test_source_detuning_direct_bivector_matches_closed_form(self):
        for eps in (F(-1,1000),F(1,1000)):
            for omega in (-2,0,F(1,3),1,2):
                self.assertTrue(check_closed_pencil(omega,lam=1+eps)['SO2_closed_inside_trial'])
            r=source_responses(lam=1+eps)
            self.assertNotEqual(r['We'],r['Wb'])

    def test_rejected_invalid_source_branch(self):
        with self.assertRaises(ValueError):source_responses(lam=0)
        with self.assertRaises(ValueError):source_responses(alpha=0)
        with self.assertRaises(ValueError):source_responses(beta=-1)
        with self.assertRaises(ValueError):source_responses(beta=F(1))

    def test_exterior_derivative_pure_longitudinal_kernel_only(self):
        for w,p in ((0,1),(2,1),(-1,2)):
            xi=(F(w),F(),F(),F(p))
            self.assertEqual(wave_field_strength(xi,xi),(0,)*6)
            z=scalar_longitudinal_response(w,p)
            self.assertEqual(z['domega_bivector_norm'],0)
            if w*w!=p*p:
                self.assertNotEqual(z['coderivative'],0)
                self.assertNotEqual(z['scalar_H'],0)
            self.assertFalse(z['full_D_gauge_quotient_available'])
        self.assertEqual(scalar_longitudinal_response()['scalar_H'],F(-3,229))

    def test_spin_two_oneforms_are_transverse_to_fourier_covector(self):
        for mode in (False,True):
            amps=_matter_oneforms(mode)
            for w,p in ((1,1),(2,3)):
                xi=(F(w),F(),F(),F(p))
                for a in amps:
                    self.assertEqual(-xi[0]*a[0]+xi[1]*a[1]+xi[2]*a[2]+xi[3]*a[3],0)

    def test_receipt_preserves_background_and_constraint_gates(self):
        r=reference_experiment()
        self.assertTrue(r['matched_lightcone_jordan_chain'])
        self.assertEqual(r['matched_extra_squared_frequency'],'1158253/1154113')
        self.assertTrue(r['detuned_plus_three_distinct_positive_roots'])
        self.assertTrue(r['detuned_minus_three_distinct_positive_roots'])
        self.assertFalse(r['full_D_has_longitudinal_gauge'])
        self.assertFalse(r['source_triplet_background_on_shell'])
        self.assertFalse(r['physical_GfE_constraint_quotient_complete'])
        self.assertFalse(r['strong_hyperbolicity_verified'])


if __name__=='__main__':
    unittest.main()
