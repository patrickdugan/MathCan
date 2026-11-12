"""TOE-13 exact curvature-sector TT, auxiliary Schur and Jordan-root lift."""
import unittest
from fractions import Fraction as F
from itertools import product
from random import Random

from research.toe.form_sector_principal import (
    ETA, _check_matrix4, linearized_ricci, metric_tensor_mode,
    background_denominators, form_sector_bilinear, tt_vector_coefficient,
    tt_form_matrix, augmented_six_mode, augmented_coefficients, lift_old_root,
    cubic_discriminant, restricted_with_vector, reference_experiment,
)
from research.toe.wave_principal import construct_symbol, evaluate_polynomial
from research.toe.tensor_subspace import default_params, at_frequency
from research.toe.mixed_principal import det


class CurvatureSectorTests(unittest.TestCase):
    def setUp(self):
        self.kw=default_params()
        self.a=self.kw['A'];self.b=self.kw['Bcurv'];self.beta=self.kw['beta']

    def test_source_sector_eigenvalue_multiplicities(self):
        theta=background_denominators(self.a,self.b,self.beta)
        self.assertEqual(theta,(F(229,250),F(247,250),F(122,125)))

    def test_0form_tt_scalar_zero_for_each_polarization(self):
        for w in (-2,-1,F(),F(1,2),1,F(3,2),3):
            for cross in (False,True):
                _,scalar=linearized_ricci((w,0,0,1),metric_tensor_mode(cross))
                self.assertEqual(scalar,0)

    def test_vector_tt_formula_direct_four_by_four(self):
        k=tt_vector_coefficient(A=self.a,Bcurv=self.b,beta=self.beta,sigma1=F(1,100))
        self.assertEqual(k,F(1,1905152))
        for w in (-3,-2,-1,0,F(1,2),1,2,3):
            a=tt_form_matrix(w,A=self.a,Bcurv=self.b,beta=self.beta,
                             sigma0=F(1,10),sigma1=F(1,100))
            expected=k*(F(w)**2-1)**2
            self.assertEqual(a,((expected,F()),(F(),expected)))

    def test_scalar_sector_tt_coefficient_zero_independent_of_strength(self):
        for s in (0,F(1,100),F(1),F(25)):
            a=tt_form_matrix(2,A=self.a,Bcurv=self.b,beta=self.beta,
                             sigma0=s,sigma1=0)
            self.assertEqual(a,((F(),F()),(F(),F())))

    def test_tt_vector_strength_scales_linearly(self):
        u=tt_form_matrix(3,A=self.a,Bcurv=self.b,beta=self.beta,
                         sigma1=F(1,100))
        v=tt_form_matrix(3,A=self.a,Bcurv=self.b,beta=self.beta,
                         sigma1=F(3,100))
        self.assertEqual(v[0][0],3*u[0][0])

    def test_background_time_matter_does_not_change_TT_spatial_operator(self):
        for shift in (F(-1,10),0,F(1,4)):
            a=tt_form_matrix(2,A=self.a,Bcurv=self.b,beta=self.beta,
                             sigma0=F(1,100),sigma1=F(1,100),time_matter=shift)
            b=tt_form_matrix(2,A=self.a,Bcurv=self.b,beta=self.beta,
                             sigma0=F(1,100),sigma1=F(1,100))
            self.assertEqual(a,b)

    def test_gauge_pure_metric_amplitudes_give_zero_ricci(self):
        rng=Random(202613)
        for _ in range(125):
            xi=tuple(F(rng.randrange(-5,6),5) for i in range(4))
            v=tuple(F(rng.randrange(-3,4),3) for i in range(4))
            h=tuple(tuple(xi[i]*v[j]+xi[j]*v[i] for j in range(4)) for i in range(4))
            ric,scalar=linearized_ricci(xi,h)
            self.assertEqual(scalar,0)
            self.assertTrue(all(x==0 for row in ric for x in row))

    def test_independent_ricci_trace_bianchi(self):
        rng=Random(12)
        for _ in range(75):
            xi=tuple(F(rng.randrange(-4,5),3) for i in range(4))
            h=[[F() for i in range(4)] for j in range(4)]
            for i in range(4):
                for j in range(i,4):
                    h[i][j]=h[j][i]=F(rng.randrange(-3,4),7)
            ric,scalar=linearized_ricci(xi,h)
            contraction=tuple(sum((ETA[mu]*xi[mu]*(ric[mu][nu]-ETA[mu]*F(1,2)*scalar*(mu==nu)) for mu in range(4)),F()) for nu in range(4))
            self.assertEqual(contraction,(F(),)*4)

    def test_ricci_pair_bilinear_symmetric(self):
        w=F(7,5);h=metric_tensor_mode(False);k=metric_tensor_mode(True)
        x=form_sector_bilinear((w,0,0,1),h,k,A=self.a,Bcurv=self.b,beta=self.beta,sigma0=1,sigma1=1)
        y=form_sector_bilinear((w,0,0,1),k,h,A=self.a,Bcurv=self.b,beta=self.beta,sigma0=1,sigma1=1)
        self.assertEqual(x['total'],y['total'])
        self.assertEqual(x['total'],0)

    def test_independent_four_by_four_determinant_TT(self):
        ts=background_denominators(self.a,self.b,self.beta)[2]
        time_theta=background_denominators(self.a,self.b,self.beta)[1]
        rng=Random(1094)
        for _ in range(100):
            w=F(rng.randrange(-3,4),2)
            d=F(rng.randrange(-3,4),20)
            ric,_=linearized_ricci((w,0,0,1),metric_tensor_mode(bool(rng.randrange(2))))
            theta0=tuple((time_theta if i==0 else ts) for i in range(4))
            theta=tuple(tuple((theta0[i] if i==j else F())-d*self.beta*ETA[i]*ric[i][j] for j in range(4)) for i in range(4))
            # The only nonzero Ricci perturbation is a transverse trace-free 2x2.
            tr=(w*w-1)/2
            expected=time_theta*ts*(ts*ts-(d*self.beta*tr)**2)
            self.assertEqual(det(theta),expected)

    def test_invalid_shapes_fail_closed(self):
        with self.assertRaises(ValueError):linearized_ricci((1,0),metric_tensor_mode())
        with self.assertRaises(ValueError):_check_matrix4([[1]*4]*3)
        with self.assertRaises(ValueError):background_denominators(100,100,1)
        with self.assertRaises(ValueError):form_sector_bilinear((1,0,0,1),metric_tensor_mode(),metric_tensor_mode(),A=1,Bcurv=1,beta=1,sigma0=-1,sigma1=0)


class CharacteristicRootTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.kw=default_params()
        cls.old=construct_symbol(**cls.kw)
        cls.lift=lift_old_root(sigma1=F(1,100),**cls.kw)
        cls.cubic=restricted_with_vector(sigma1=F(1,100),**cls.kw)

    def test_old_jordan_root_is_lifted_in_six_mode_symbol(self):
        self.assertEqual(self.lift['root_rank'],6)
        self.assertTrue(self.lift['old_root_lifted'])
        self.assertNotEqual(self.lift['root_determinant'],(F(),F()))

    def test_old_root_lift_has_exact_factor(self):
        self.assertEqual(self.lift['root_determinant'],self.lift['expected'])
        self.assertEqual(self.lift['root_determinant'][1],0)
        self.assertGreater(self.lift['root_determinant'][0],0)

    def test_zero_vector_coupling_retains_old_root(self):
        k=tt_vector_coefficient(A=self.kw['A'],Bcurv=self.kw['Bcurv'],beta=self.kw['beta'],sigma1=0)
        self.assertEqual(k,0)
        self.assertEqual(evaluate_polynomial(self.old.determinant,self.old.doubled_gravity_root),0)
        with self.assertRaises(ValueError):lift_old_root(sigma1=0,**self.kw)

    def test_augmented_six_mode_agrees_with_polynomial_at_rational_frequency(self):
        coeff=augmented_coefficients(sigma0=F(1,100),sigma1=F(1,100),**self.kw)
        for w in (-2,-1,F(),1,2,F(3,4)):
            self.assertEqual(augmented_six_mode(w,sigma0=F(1,100),sigma1=F(1,100),**self.kw),at_frequency(coeff,w))

    def test_form_scalar_only_leaves_tensor_symbol_unchanged(self):
        coeff=augmented_coefficients(sigma0=F(1),sigma1=0,**self.kw)
        original=augmented_coefficients(sigma0=0,sigma1=0,**self.kw)
        self.assertEqual(coeff,original)

    def test_form_vector_adds_exact_quartic(self):
        coeff=augmented_coefficients(sigma1=F(1,100),**self.kw)
        raw=augmented_coefficients(sigma1=0,**self.kw)
        k=self.lift['vector_coefficient']
        for i in (0,1):
            self.assertEqual(tuple(a-b for a,b in zip(coeff[(i,i)],raw[(i,i)])),(k,F(),-2*k,F(),k))
        self.assertEqual(coeff[(0,1)],raw[(0,1)])

    def test_restricted_cubic_negative_discriminant(self):
        self.assertLess(self.cubic['discriminant'],0)
        self.assertTrue(self.cubic['one_real_two_complex_x'])
        self.assertTrue(self.cubic['one_positive_real_x'])

    def test_restricted_formal_complex_pair_persists_at_small_coupling(self):
        for scale in (1,100,10000):
            out=restricted_with_vector(sigma1=F(1,100*scale),**self.kw)
            self.assertLess(out['discriminant'],0)
            self.assertLess(out['value_at_old_root'],0)

    def test_cubic_discriminant_known_factors(self):
        self.assertEqual(cubic_discriminant((0,-1,0,1)),4)
        self.assertEqual(cubic_discriminant((0,1,0,1)),-4)
        self.assertEqual(cubic_discriminant((-1,3,-3,1)),0)

    def test_old_root_is_not_unit_lightcone(self):
        self.assertNotEqual(self.old.doubled_gravity_root,1)
        self.assertLess(self.old.doubled_gravity_root,1)

    def test_full_theory_gate_is_explicit(self):
        receipt=reference_experiment()
        self.assertFalse(receipt['full_GfE_constraints_derived'])
        self.assertFalse(receipt['full_theory_strong_hyperbolicity_verified'])
        self.assertTrue(receipt['root_det_nonzero'])

if __name__ == '__main__':unittest.main()
