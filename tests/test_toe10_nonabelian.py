"""TOE-10: proposed SU(2)^2 operator, GR+YM Krein crossing, gauge medium EL."""
import json
import unittest
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from random import Random

from research.toe.yang_mills_triads import Triad, einstein_ym_rk4_one_step
from research.toe.lorentz_bivector import raised_gram6, source_block
from research.toe.nonabelian_gfe import (
    IDENTITY, Medium, canonical_gr_spectrum, covariant_colour_gram,
    critical_example, gr_background, gr_spectrum, invariants,
    lorentz_colour_operator, normalized_mixed_flow, rat, reference_experiment,
    rotation3,
)

R = ((F(3,5),-F(4,5),F(0)),(F(4,5),F(3,5),F(0)),(F(0),F(0),F(1)))
S = ((F(1),F(0),F(0)),(F(0),F(0),-F(1)),(F(0),F(1),F(0)))


class GaugeAndSpectrum(unittest.TestCase):
    def setUp(self):
        self.T = (Triad(1,2,1),Triad(0,1,1))
        self.k = F(1,10)
        self.beta = F(1,100)
        self.alpha = 6*self.beta*self.k

    def test_source_relative_adjoint_contraction(self):
        m = covariant_colour_gram(self.T)
        self.assertEqual(m,covariant_colour_gram(self.T,(R,S)))
        self.assertEqual(m,covariant_colour_gram(self.T,(S,R)))
        self.assertEqual(m[0][0],F(5))
        self.assertEqual(m[3][3],F(1))
        self.assertEqual(m[0][3],F(2))

    def test_lorentz_sign_and_full_matrix(self):
        m = lorentz_colour_operator(self.T,(R,S))
        self.assertEqual(m,raised_gram6([2,1],[1,0]))
        self.assertEqual(m[0][0],-5)
        self.assertEqual(m[0][3],2)
        self.assertEqual(m[3][0],-2)

    def test_invalid_non_gauge_rotation_rejected(self):
        with self.assertRaises(ValueError):rotation3(((2,0,0),(0,1,0),(0,0,1)))
        with self.assertRaises(ValueError):rotation3(((-1,0,0),(0,1,0),(0,0,1)))
        with self.assertRaises(ValueError):covariant_colour_gram(self.T,(R,))
        with self.assertRaises(ValueError):covariant_colour_gram([])
        with self.assertRaises(ValueError):rat(True)

    def test_spectral_boundary_exact(self):
        x=canonical_gr_spectrum(self.T,1,self.k,self.beta)
        self.assertEqual(x['s'],6)
        self.assertEqual(x['c'],2)
        self.assertEqual(x['Hdot'],-F(3,5))
        self.assertEqual(x['Lambda'],F(21,10))
        self.assertEqual(x['block'].theta_e,F(481,500))
        self.assertEqual(x['block'].theta_b,F(493,500))
        self.assertEqual(x['block'].discriminant,0)
        self.assertFalse(x['block'].diagonalizable)
        self.assertEqual(x['delta_dot'],-F(54,15625))

    def test_canonical_normalization_gap_no_match(self):
        for e1,e2 in product([F(0),F(1,3),F(2)],repeat=2):
            ts=(Triad(1,e1,1),Triad(0,e2,1))
            x=canonical_gr_spectrum(ts,1,self.k,self.beta)
            self.assertEqual(x['gap'],-4*self.beta*self.k*x['s'])
            self.assertLess(x['gap'],0)

    def test_critical_ratio_and_defectiveness(self):
        x=canonical_gr_spectrum(self.T,1,self.k,self.beta)
        self.assertEqual(abs(x['r']),F(1,3))
        self.assertFalse(x['block'].exact_positive_real)
        self.assertFalse(x['block'].diagonalizable)

    def test_positive_real_start_to_complex_pair(self):
        start,ts=critical_example(F(1,100000))
        self.assertGreater(start['block'].discriminant,0)
        self.assertTrue(start['block'].exact_positive_real)
        next_h,next_t=einstein_ym_rk4_one_step(ts,1,self.k,F(1,10000))
        end=canonical_gr_spectrum(next_t,next_h,self.k,self.beta)
        self.assertLess(end['block'].discriminant,0)
        self.assertGreater(end['block'].trace,0)
        self.assertGreater(end['block'].determinant,0)
        self.assertFalse(end['block'].exact_positive_real)

    def test_step_halving_and_crossing(self):
        ts=(Triad(1,2,1),Triad(0,F(100001,100000),1))
        x,t1=einstein_ym_rk4_one_step(ts,1,self.k,F(1,10000))
        mid,s1=einstein_ym_rk4_one_step(ts,1,self.k,F(1,20000))
        y,t2=einstein_ym_rk4_one_step(s1,mid,self.k,F(1,20000))
        self.assertLess(abs(float(x-y)),1e-13)
        self.assertLess(abs(float(t1[0].electric-t2[0].electric)),1e-12)
        self.assertLess(canonical_gr_spectrum(t2,y,self.k,self.beta)['block'].discriminant,0)

    def test_ym_normalized_flow_exact(self):
        random=Random(20261111)
        for _ in range(120):
            ts=[Triad(F(random.randint(-4,4),5),F(random.randint(-5,5),5),1),
                Triad(F(random.randint(-4,4),5),F(random.randint(-5,5),5),F(2))]
            H=F(random.randint(-3,5),4)
            x=normalized_mixed_flow(ts,H)
            self.assertEqual(x['sdot'],-4*H*x['s'])
            self.assertEqual(x['cdot'],-4*H*x['c']+x['torque'])
            self.assertEqual(x['rdot'],x['torque']/x['s'])

    def test_spectrum_eigenvalue_cases(self):
        # Both the strictly real domain and the complex region are nonempty.
        t0=(Triad(1,2,1),Triad(0,2,1))
        t1=(Triad(1,2,1),Triad(0,0,1))
        self.assertTrue(canonical_gr_spectrum(t0,1,self.k,self.beta)['block'].discriminant>0)
        self.assertLess(canonical_gr_spectrum(t1,1,self.k,self.beta)['block'].discriminant,0)

    def test_flavor_vs_gauge(self):
        # Color rotations are independent SU(2) gauge choices; a rotation in
        # flavor space is not itself an SU(2) gauge transformation.
        x=lorentz_colour_operator(self.T,(S,R))
        y=lorentz_colour_operator(self.T,(IDENTITY,IDENTITY))
        self.assertEqual(x,y)

    def test_source_fixture(self):
        r=reference_experiment()
        self.assertEqual(r['schema'],'mathcan.toe10.nonabelian.v1')
        self.assertTrue(r['initial_positive_real'])
        self.assertEqual(r['boundary_discriminant_derivative'],'-54/15625')
        fixture=Path(__file__).resolve().parents[1]/'research/toe/fixtures/toe10_nonabelian_synthetic.json'
        self.assertEqual(r,json.loads(fixture.read_text()))


class MediumELTests(unittest.TestCase):
    def setUp(self):
        self.ts=(Triad(F(1),F(2),1),Triad(0,F(100001,100000),1))
        self.H=F(1)
        self.k=F(1,10)
        self.beta=F(1,100)
        self.alpha=6*self.beta*self.k
        self.Hdot=-self.k*sum(x*x for t in self.ts for x in (t.electric,t.magnetic))
        self.Hddot=-4*self.H*self.Hdot

    def test_bare_yang_mills_recovered(self):
        m=Medium(self.alpha,self.beta,0)
        r=m.electric_acceleration(self.ts,self.H,self.Hdot,self.Hddot)
        self.assertEqual(r['electric_dot'],tuple(t.tangent(self.H)[1] for t in self.ts))
        self.assertEqual(r['kinetic_det'],9)

    def test_nonzero_medium_changes_matter_eom(self):
        m=Medium(self.alpha,self.beta,F(1,100))
        r=m.electric_acceleration(self.ts,self.H,self.Hdot,self.Hddot)
        self.assertGreater(r['kinetic_det'],0)
        self.assertNotEqual(r['electric_dot'],tuple(t.tangent(self.H)[1] for t in self.ts))
        p=r['local']['momentum']
        self.assertNotEqual(p[0],3*self.ts[0].electric)

    def test_hessian_symmetry(self):
        m=Medium(self.alpha,self.beta,F(1,1000))
        h=m.local(self.ts,self.H,self.Hdot)['hessian']
        self.assertEqual(h[0][1],h[1][0])

    def test_constitutive_momenta_against_finite_difference(self):
        m=Medium(self.alpha,self.beta,F(1,500))
        r=m.local(self.ts,self.H,self.Hdot)
        for i in range(2):
            eps=F(1,100000)
            plus=list(self.ts);minus=list(self.ts)
            t=self.ts[i]
            plus[i]=Triad(t.psi,t.electric+eps,t.coupling)
            minus[i]=Triad(t.psi,t.electric-eps,t.coupling)
            cen=(m.local(plus,self.H,self.Hdot,require_spectral=False)['momentum'][i]
                 -m.local(minus,self.H,self.Hdot,require_spectral=False)['momentum'][i])/(2*eps)
            self.assertAlmostEqual(float(cen),float(r['hessian'][i][i]),places=8)

    def test_medium_mixed_hessian_against_magnetic_difference(self):
        # Magnetic amplitude in the constitutive map is an independent jet.
        # Compare analytical p(E,B) derivative to a direct rational formula
        # with independently displaced B, before enforcing B=g psi².
        m=Medium(self.alpha,self.beta,F(1,1000))
        r=m.local(self.ts,self.H,self.Hdot)
        e,b,c=invariants(self.ts)
        a,beta=m.alpha,m.beta
        D=r['block'].determinant
        te,tb=r['block'].theta_e,r['block'].theta_b
        n0=tb*self.ts[0].electric-a*c*self.ts[0].magnetic
        deriv=(2*a*self.ts[1].magnetic*self.ts[0].electric
               -a*(self.ts[1].electric*self.ts[0].magnetic))/D
        deriv-=n0*(2*a*te*self.ts[1].magnetic+2*a*a*c*self.ts[1].electric)/(D*D)
        self.assertEqual(r['mixed_hessian'][0][1],m.sigma*6*a*deriv)

    def test_curvature_jet_response_independent(self):
        m=Medium(self.alpha,self.beta,F(1,1000))
        r=m.local(self.ts,self.H,self.Hdot)
        dt=F(1,10000)
        # p_A is the derivative with respect to A, i.e. Hdot at fixed H.
        r_plus=m.local(self.ts,self.H,self.Hdot+dt,require_spectral=False)
        r_minus=m.local(self.ts,self.H,self.Hdot-dt,require_spectral=False)
        for i in range(2):
            estimate=(r_plus['momentum'][i]-r_minus['momentum'][i])/(2*dt)
            self.assertAlmostEqual(float(estimate),float(r['curvature_A'][i]),places=8)

    def test_medium_spectral_fail_closed(self):
        m=Medium(self.alpha,self.beta,F(1,100))
        boundary=(Triad(1,2,1),Triad(0,1,1))
        with self.assertRaises(ValueError):m.local(boundary,self.H,F(-3,5))
        with self.assertRaises(ValueError):m.local((Triad(1,2,1),Triad(0,0,1)),self.H,F(-1,2))

    def test_medium_invalid_params(self):
        for bad in ((0,1,0),(1,-1,0),(1,1,-1)):
            with self.assertRaises(ValueError):Medium(*bad)
        with self.assertRaises(ValueError):Medium(1,1,0).electric_acceleration([Triad(1,1,1)],1,0,0)

    def test_small_medium_negative_discriminant_rate(self):
        s=invariants(self.ts)
        for strength in (F(0),F(1,100000),F(1,1000),F(1,100)):
            m=Medium(self.alpha,self.beta,strength)
            y=m.electric_acceleration(self.ts,self.H,self.Hdot,self.Hddot)
            edot=y['electric_dot']
            bdots=[t.magnetic_dot(self.H) for t in self.ts]
            sdot=sum((2*t.electric*edot[i]+2*t.magnetic*bdots[i]
                      for i,t in enumerate(self.ts)),F(0))
            cdot=sum((edot[i]*t.magnetic+t.electric*bdots[i]
                       for i,t in enumerate(self.ts)),F(0))
            gap=-self.alpha*(s[0]+s[1])-2*self.beta*self.Hdot
            gdot=-self.alpha*sdot-2*self.beta*self.Hddot
            discdot=2*gap*gdot-8*self.alpha*self.alpha*s[2]*cdot
            self.assertLess(discdot,0)
            self.assertGreater(y['kinetic_det'],0)

    def test_medium_on_orthogonal_color_gauges(self):
        # Local scalar momenta depend only on color-invariant E/B contractions.
        m=Medium(self.alpha,self.beta,F(1,1000))
        self.assertEqual(covariant_colour_gram(self.ts,(IDENTITY,IDENTITY)),
                         covariant_colour_gram(self.ts,(R,S)))
        self.assertTrue(m.local(self.ts,self.H,self.Hdot)['block'].exact_positive_real)


if __name__ == '__main__':
    unittest.main()
