"""Exact-rational test of conditional Ricci response and algebraic cone escape."""
import unittest
from fractions import Fraction as Q
from itertools import product
from random import Random
from research.toe.multiplet_cone import (
    cone,principal_q4,target_matter_split,nonnegative_algebraic_compensation,
    wedge_oneforms,homogeneous_scalar_wedge,trajectory_diagnostic,
    vector_response,det3,scalar_isotropic)
from research.toe.ricci_response import (
    ricci_d_components,independent_operator_components,geometry,
    ricci_lift_from_reduced_derivatives,double_divergence)
from research.toe.covariant_tensors import responses,tt_symbol
from research.toe.gfield_scalar_flrw import reference_experiment

class ConeTests(unittest.TestCase):
    def test_source_vacuum_split(self):
        for hdot in (Q(-1,5),Q(-1,100),Q(0),Q(3,50)):
            c=cone(Q(1,100),Q(3,50),Q(1),hdot)
            old=responses(Q(1,100),Q(1),hdot)
            self.assertEqual(c.we,old['WE'])
            self.assertEqual(c.wb,old['WB'])
            self.assertEqual(c.ws,old['Ws'])
            self.assertEqual(c.discriminant,tt_symbol(c.ws,c.we,c.wb)['discriminant'])

    def test_algebraic_compensation_exact(self):
        b=Q(1,100);alpha=Q(3,50)
        for q,k in product((Q(-3,50),Q(-1,100),Q(0),Q(1,50)),(Q(-1,100),Q(0),Q(2,100))):
            mE,mB=nonnegative_algebraic_compensation(b,alpha,q,k)
            self.assertGreaterEqual(min(mE,mB),0)
            self.assertEqual(mE-mB,target_matter_split(b,alpha,q,k))
            x=cone(b,alpha,1,q,mE,mB,k)
            self.assertEqual(x.discriminant,0)
            self.assertEqual(principal_q4(x),0)

    def test_uncompensated_negative_discriminant(self):
        for q in (Q(-1,20),Q(-1,100),Q(1,100)):
            c=cone(Q(1,100),Q(3,50),1,q)
            self.assertLess(c.discriminant,0)
            self.assertGreater(principal_q4(c),0)

    def test_mismatch_quadratic_exact(self):
        b=Q(1,100);alpha=Q(3,50);h=Q(-1,100)
        base_e,base_b=nonnegative_algebraic_compensation(b,alpha,h)
        for e in (Q(-1,100),Q(-1,1000),Q(0),Q(1,1000),Q(1,100)):
            x=cone(b,alpha,1,h,base_e+Q(1,5)+e,base_b+Q(1,5))
            self.assertEqual(x.response_split,alpha*e)
            self.assertEqual(x.discriminant,-4*x.ws*x.ws*alpha*alpha*e*e/(x.theta_e**2*x.theta_b**2))

    def test_matched_principal_lightcone_only(self):
        a,b=nonnegative_algebraic_compensation(Q(1,100),Q(3,50),Q(-1,100))
        x=cone(Q(1,100),Q(3,50),1,Q(-1,100),a,b)
        for w in (Q(0),Q(1,4),Q(1),Q(2)):
            self.assertEqual(principal_q4(x,w),x.ws*x.ws/Q(2)*(w-1)**2+2*x.we*x.we*(w-1)**2)

    def test_scalar_gradient_wedges_identically_vanish(self):
        for u,v in product(range(-6,7),repeat=2):
            self.assertEqual(homogeneous_scalar_wedge(u,v),(0,)*6)
        self.assertNotEqual(wedge_oneforms((1,0,0,0),(0,1,0,0)),(0,)*6)

    def test_two_single_bivectors_cannot_make_nonzero_isotropic_E_response(self):
        from itertools import product
        vs=list(product((-1,0,1),repeat=3))
        for e1,e2 in product(vs,repeat=2):
            m=vector_response([e1,e2])
            self.assertEqual(det3(m),0)
            if scalar_isotropic(m):
                self.assertEqual(m[0][0],0)

    def test_three_spatial_vectors_can_form_exact_isotropic_response(self):
        m=vector_response([(1,0,0),(0,1,0),(0,0,1)])
        self.assertTrue(scalar_isotropic(m))
        self.assertEqual(det3(m),1)

    def test_negative_induced_metric_rejected(self):
        with self.assertRaises(ValueError):cone(1,1,1,1)
        with self.assertRaises(ValueError):nonnegative_algebraic_compensation(1,0,1)
        with self.assertRaises(ValueError):nonnegative_algebraic_compensation(1,1,0,baseline=-1)

    def test_response_baseline_gauge(self):
        b=Q(1,100);a=Q(3,50);q=Q(-1,100)
        e0,b0=nonnegative_algebraic_compensation(b,a,q)
        for offset in (Q(0),Q(1,5),Q(3,10)):
            c=cone(b,a,1,q,e0+offset,b0+offset)
            self.assertEqual(c.response_split,0)
            self.assertEqual(c.discriminant,0)
            self.assertNotEqual(c.theta_e,cone(b,a,1,q,e0,b0).theta_e) if offset else None

    def test_synthetic_reference_trajectory(self):
        data=trajectory_diagnostic(reference_experiment()['curve'])
        self.assertEqual(len(data),6)
        self.assertTrue(all(x['compensated_discriminant']=='0' for x in data))
        self.assertTrue(all(x['theta_E']>0 and x['theta_B']>0 for x in data))
        self.assertTrue(all(x['uncompensated_discriminant']<0 for x in data))


class RicciResponseTests(unittest.TestCase):
    def test_exact_operator_contractions(self):
        r=Random(118071)
        for _ in range(700):
            h=Q(r.randint(-8,8),10)
            d=Q(r.randint(-5,5),10)
            nums=[Q(r.randint(-10,10),7) for i in range(6)]
            self.assertEqual(ricci_d_components(h,d,*nums)['D00'],independent_operator_components(h,d,*nums)['D00'])
            self.assertEqual(ricci_d_components(h,d,*nums)['Ds'],independent_operator_components(h,d,*nums)['Ds'])

    def test_standard_fr_trace_scalar_limit(self):
        # P^(mu nu)=f_R*g^(mu nu) implies D00=3H*f_R_dot,
        # Ds=-f_R_ddot-2H*f_R_dot
        for H in (Q(0),Q(1,3),Q(3,2)):
            for first in (Q(-1),Q(0),Q(2,7)):
                f0=Q(4,7); fd2=Q(11,10)
                d=ricci_d_components(H,Q(1,3),f0,f0,first,first,fd2,fd2)
                self.assertEqual(d['D00'],3*H*first)
                self.assertEqual(d['Ds'],-fd2-2*H*first)

    def test_constant_einstein_response_vanishes(self):
        for H,q in product((Q(0),Q(1),Q(3)),(Q(-1,5),Q(0),Q(1,10))):
            p=Q(18,7)
            d=ricci_d_components(H,q,p,p,0,0,0,0)
            self.assertEqual((d['D00'],d['Ds'],d['trace']),(0,0,0))

    def test_ricci_lift_gr(self):
        p=Q(3,100)
        U,V,*_=ricci_lift_from_reduced_derivatives(6*p,6*p,0,0,0,0)
        self.assertEqual((U,V),(p,p))

    def test_exact_gradient_lift(self):
        for a,b in product((0,Q(6),Q(7,3)),(0,Q(5),Q(3,2))):
            U,V,*_=ricci_lift_from_reduced_derivatives(a,b,0,0,0,0)
            self.assertEqual(-3*U+3*V,-a+b)
            self.assertEqual(6*V,b)

    def test_trace_components(self):
        H=Q(2);hdot=Q(-1,20)
        d=ricci_d_components(H,hdot,1,2,Q(2,3),Q(7,8),Q(9,10),Q(-1,5))
        self.assertEqual(d['trace'],-d['D00']+3*d['Ds'])
        self.assertEqual(geometry(H,hdot),hdot+3*H*H)
        self.assertEqual(double_divergence(0,0,1,1,0,0,0),0)

if __name__=='__main__': unittest.main()
