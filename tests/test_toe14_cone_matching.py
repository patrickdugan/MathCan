"""TOE-14 exact rational cone and resolvent regression tests."""
import unittest
from fractions import Fraction as F
from random import Random
from research.toe.cone_matching import (
    cone_certificate, two_cone_coefficients, quadratic_discriminant,
    vacuum_inverse_responses, vacuum_tt_benchmark,
    toe13_resolvent_certificate, fourier_phase_two_mode,
    minkowski_quadratic_gravity,reference_experiment,
    TOE13_R,TOE13_C1,
)


class ConeIdentityTests(unittest.TestCase):
    def test_exhaustive_rational_discriminant(self):
        vals=(F(-3,2),F(-1,2),F(0),F(1,3),F(3,2),F(2))
        for a in (F(1,10),F(1),F(9,2)):
            for b in (F(1,5),F(7,3)):
                for u in vals:
                    for v in vals:
                        c=cone_certificate(a,b,u,v)
                        self.assertEqual(c['discriminant'],-4*a*b*(u-v)**2)
                        self.assertEqual(c['real_characteristic'],u==v)
                        self.assertEqual(c['discriminant']==0,u==v)
                        self.assertEqual(c['imaginary_squared']==0,u==v)
                        x=F(3,4)
                        coeff=c['coefficients']
                        self.assertEqual(coeff[0]+coeff[1]*x+coeff[2]*x*x,
                                         a*(x-u)**2+b*(x-v)**2)

    def test_fails_closed_for_nonpositive_weights(self):
        for a,b in ((0,1),(1,0),(-1,1),(1,-1)):
            with self.assertRaises(ValueError):
                two_cone_coefficients(a,b,1,2)
        with self.assertRaises(ValueError): quadratic_discriminant((1,2,0))
        with self.assertRaises(TypeError): cone_certificate(0.5,1,1,2)

    def test_representative_complex_pairs(self):
        c=cone_certificate(F(1,2),2,1,2)
        self.assertEqual(c['coefficients'],(F(17,2),-9,F(5,2)))
        self.assertEqual(c['discriminant'],-4)
        self.assertEqual(c['center'],F(9,5))
        self.assertEqual(c['imaginary_squared'],F(4,25))


class VacuumSourceComparisonTests(unittest.TestCase):
    def test_exact_response_values(self):
        self.assertEqual(vacuum_inverse_responses(beta=F(1,100),accel=F(2,5),spatial=1),
                         (F(125,122),F(125,124),F(50,49)))

    def test_pereira_two_square_form_and_non_einstein_gap(self):
        v=vacuum_tt_benchmark(beta=F(1,100),accel=F(2,5),spatial=1)
        self.assertEqual(v['discriminant'],F(-87890625,137371044496))
        self.assertLess(v['discriminant'],0)
        self.assertFalse(v['background_cone_matching'])
        self.assertFalse(v['real_characteristic'])
        self.assertNotEqual(v['WE'],v['WB'])
        ws,we,wb=v['Ws'],v['WE'],v['WB']
        # Pereira Eq. (25), checked against the independent general-cone oracle.
        self.assertEqual(v['discriminant'],-4*ws**2*(we-wb)**2)
        # Eq. (26) gives the exact center and imaginary-square formula.
        self.assertEqual(v['center'],(ws**2+4*we*wb)/(ws**2+4*we**2))
        self.assertEqual(v['imaginary_squared'],
                         (2*ws*(we-wb)/(ws**2+4*we**2))**2)

    def test_einstein_background_cone_matching(self):
        for curvature in (-1,F(-1,2),0,F(2,5),1):
            v=vacuum_tt_benchmark(beta=F(1,100),accel=curvature,spatial=curvature)
            self.assertEqual(v['discriminant'],0)
            self.assertTrue(v['background_cone_matching'])
            self.assertEqual(v['center'],1)
            self.assertTrue(v['real_characteristic'])

    def test_positive_weights_both_have_same_root_locus(self):
        for w in (F(1,2),1,F(7,3)):
            c=vacuum_tt_benchmark(beta=F(1,100),accel=F(2,5),spatial=1,one_form_weight=w)
            self.assertLess(c['discriminant'],0)
            self.assertEqual(c['discriminant'], -8*w*c['Ws']**2*(c['WE']-c['WB'])**2)

    def test_positive_denominator_gates(self):
        with self.assertRaises(ValueError):
            vacuum_tt_benchmark(beta=1,accel=1,spatial=1)
        with self.assertRaises(ValueError):
            vacuum_tt_benchmark(beta=F(-1,10),accel=0,spatial=0)
        with self.assertRaises(ValueError):
            vacuum_tt_benchmark(beta=F(1,100),accel=0,spatial=0,one_form_weight=0)

    def test_minkowski_low_curvature_benchmark(self):
        x=minkowski_quadratic_gravity(beta=F(1,100))
        self.assertEqual(x['R_coefficient'],F(3,100))
        self.assertEqual(x['Ricci_squared_coefficient'],F(1,4000))
        self.assertEqual(x['scalar_mass_squared'],60)
        self.assertEqual(x['spin2_mass_squared'],-120)
        self.assertEqual(x['spin2_mass_squared'],-2*x['scalar_mass_squared'])


class RestrictedSymbolTests(unittest.TestCase):
    def test_exact_toe13_resolvent_bound(self):
        v=toe13_resolvent_certificate()
        self.assertEqual(v['old_root'],TOE13_R)
        self.assertEqual(v['vector_coefficient'],TOE13_C1)
        self.assertEqual(v['metric_diagonal'],F(144144108036009,463045288448000000000000))
        self.assertGreater(v['inverse_metric_diagonal'],3_200_000_000)
        self.assertEqual(v['inverse_metric_diagonal']*v['metric_diagonal'],1)

    def test_toe13_old_root_inputs_fail_closed(self):
        with self.assertRaises(ValueError):toe13_resolvent_certificate(r=1)
        with self.assertRaises(ValueError):toe13_resolvent_certificate(c1=0)

    def test_fourier_hermitian_congruence_two_mode(self):
        rng=Random(202614)
        for i in range(200):
            a,b,c=(F(rng.randrange(-11,12),rng.randrange(1,13)) for _ in range(3))
            out=fourier_phase_two_mode(a,b,c)
            self.assertEqual(out['formal_determinant'],a*c-b*b)
            self.assertEqual(out['fourier_determinant'],a*c-b*b)
            upper,lower=out['entries'][0][1],out['entries'][1][0]
            self.assertEqual(upper,(0,-b))
            self.assertEqual(lower,(0,b))

    def test_explicit_scope_receipt(self):
        x=reference_experiment()
        self.assertFalse(x['coupled_GfE_YM_constraints_derived'])
        self.assertFalse(x['physical_hyperbolicity_verified'])
        self.assertTrue(x['vacuum_source_normalization_independently_verified'])


if __name__=='__main__':unittest.main()
