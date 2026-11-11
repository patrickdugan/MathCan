"""TOE-12 exact six-mode tensor/helicity subspace and Krein-boundary tests."""
from fractions import Fraction as F
import unittest

from research.toe.tensor_subspace import (
    default_params,bilinear_matrix,independent_polarization_matrix,
    interpolate_tensor,at_frequency,tensor_certificate,
    factored_tensor_at_root,field_determinant,_field_evaluate,_fit_polynomial,
)
from research.toe.wave_principal import construct_symbol

class FullTensorProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.opts=default_params()
        cls.w=construct_symbol(**cls.opts)
        cls.coeff=interpolate_tensor(**cls.opts)
        cls.report=tensor_certificate(**cls.opts)

    def test_two_helicities_and_both_gauge_flavors(self):
        self.assertEqual(len(self.coeff),21)
        self.assertEqual(len(at_frequency(self.coeff,0)),6)
        self.assertTrue(self.report['parity_sensitive_cross_helicity_coupling'])

    def test_independent_6x6_trace_polarization(self):
        for omega in (F(0),F(1)):
            self.assertEqual(bilinear_matrix(omega,**self.opts),
                             independent_polarization_matrix(omega,**self.opts))

    def test_general_frequency_polynomial_interpolation(self):
        for omega in (F(-7,2),F(0),F(9,4)):
            self.assertEqual(at_frequency(self.coeff,omega),
                             bilinear_matrix(omega,**self.opts))

    def test_metric_quartic_double_root_both_helicities(self):
        r=self.w.doubled_gravity_root
        for i in (0,1):
            c=self.coeff[(i,i)]
            self.assertEqual(c,(c[4]*r*r,F(),-2*c[4]*r,F(),c[4]))
            self.assertNotEqual(c[4],0)
        self.assertEqual(self.coeff[(0,1)],(F(),)*5)

    def test_metric_gauge_mixed_root_factors(self):
        r=self.w.doubled_gravity_root
        for i in (0,1):
            for j in (2,3,4,5):
                c=self.coeff[(i,j)]
                self.assertEqual(c,(-r*c[2],-r*c[3],c[2],c[3]))

    def test_parity_sensitive_terms_present(self):
        plus_cross=self.coeff[(0,3)]
        cross_plus=self.coeff[(1,2)]
        self.assertNotEqual(plus_cross[0],0)
        self.assertEqual(plus_cross[0],-cross_plus[0])
        self.assertEqual(plus_cross[1],0)
        self.assertEqual(cross_plus[1],0)

    def test_exact_root_characteristic_multiplicity_four(self):
        r=self.w.doubled_gravity_root
        value=factored_tensor_at_root(self.coeff,r)
        self.assertEqual(value['root_det_multiplicity'],4)
        self.assertEqual(value['root_nullity'],2)
        self.assertEqual(value['gauge_rank'],4)
        self.assertEqual(value['reduced_rank'],6)
        self.assertNotEqual(value['reduced_determinant'],(F(),F()))

    def test_full_six_dimensional_reduced_determinant_is_rational(self):
        v=self.report['reduced_determinant']
        self.assertNotEqual(F(v[0]),0)
        self.assertEqual(F(v[1]),0)
        self.assertFalse(self.report['full_tensor_wave_sector_complete'])

    def test_krein_neighboring_two_flavor_backgrounds(self):
        for E2 in (F(999,1000),F(1),F(1001,1000)):
            opts=dict(self.opts,electric=(2,E2))
            z=tensor_certificate(**opts)
            self.assertEqual(z['root_nullity'],2)
            self.assertEqual(z['determinant_divisible_by_delta_power'],4)

    def test_field_determinant_simple_example(self):
        r=F(2)
        # determinant of [sqrt(2),0;0,sqrt(2)] is exactly 2.
        m=(((F(),F(1)),(F(),F())),
           ((F(),F()),(F(),F(1))))
        d,rank=field_determinant(m,r)
        self.assertEqual(d,(F(2),F()))
        self.assertEqual(rank,2)

    def test_field_singular_and_rational_square_rejected(self):
        with self.assertRaises(ValueError):field_determinant((((1,0),),),F(4))
        d,rank=field_determinant((((0,0),),),F(2))
        self.assertEqual((d,rank),((F(),F()),0))

    def test_interpolation_simple_quartic(self):
        nodes=(-2,-1,0,1,2)
        values=tuple(3*x**4-2*x**3+5*x-7 for x in nodes)
        self.assertEqual(_fit_polynomial(nodes,values),(-7,5,0,-2,3))

    def test_exact_field_evaluation(self):
        self.assertEqual(_field_evaluate((1,2,3,4,5),F(2)),(F(27),F(10)))

    def test_explicit_full_theory_omission_flags(self):
        self.assertIs(self.report['Gfield_0_1_form_or_metric_constraints_complete'],False)
        self.assertFalse(self.report['full_tensor_wave_sector_complete'])

if __name__=='__main__':unittest.main()
