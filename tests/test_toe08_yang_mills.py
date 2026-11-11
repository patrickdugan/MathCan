"""TOE-08: action-derived two-SU(2) cosmological triad and 2-form Gram audit."""
import unittest
from fractions import Fraction as Q
from itertools import product
from random import Random

from research.toe.yang_mills_triads import (
    Triad, stress_tensor, energy_pressure, energy_rate, response_blocks,
    response_matrix, det_exact, gram_det_formula, two_multiplet_wedge,
    induced_response, response_derivatives, target_Hdot_for_diagonal_matching,
    symmetric_two_triad_example, rk4_one_step
)

class TwoTriadTests(unittest.TestCase):
    def setUp(self):
        self.x = symmetric_two_triad_example()
        self.ts = self.x['triads']

    def test_exact_example(self):
        self.assertEqual((self.x['me'],self.x['mb'],self.x['mix']),
                         (Q(1,512),Q(1,128),Q(0)))
        self.assertEqual(self.x['Hdot'],Q(-9,512))
        self.assertEqual(self.x['mixDot'],Q(-3,1024))
        self.assertEqual(self.x['thetaMixDot'],Q(-9,51200))

    def test_stress_exact_isotropic(self):
        rho,p=energy_pressure(self.ts)
        self.assertEqual((rho,p),(Q(15,1024),Q(5,1024)))
        T=stress_tensor(self.ts)
        self.assertEqual(T,((rho,Q(0),Q(0),Q(0)),
                            (Q(0),p,Q(0),Q(0)),
                            (Q(0),Q(0),p,Q(0)),
                            (Q(0),Q(0),Q(0),p)))
        self.assertEqual(-T[0][0]+sum(T[i][i] for i in range(1,4)),0)

    def test_stress_anisotropy_absent_many_states(self):
        for a,b,g in product((Q(-1,3), Q(0),Q(5,12)),
                             (Q(-1,4),Q(0),Q(1,5)),(Q(1,3),Q(1))):
            t=Triad(a,b,g)
            rho,p=energy_pressure((t,))
            self.assertEqual(stress_tensor((t,)), tuple(tuple(
                rho if i==j==0 else p if i==j else Q(0)
                for j in range(4)) for i in range(4)))

    def test_energy_is_radiation_under_ym(self):
        rng=Random(20261111)
        for _ in range(150):
            t=Triad(Q(rng.randint(-8,8),16),Q(rng.randint(-8,8),16),Q(1,2))
            H=Q(rng.randint(-5,7),6)
            rho,p=energy_pressure((t,))
            self.assertEqual(energy_rate((t,),H),-3*H*(rho+p))

    def test_two_multiplet_conservation(self):
        rho,p=energy_pressure(self.ts)
        self.assertEqual(energy_rate(self.ts,self.x['H']),-4*self.x['H']*rho)

    def test_field_strength_magnetic_psi_squared(self):
        for t in self.ts:
            self.assertEqual(t.magnetic,t.coupling*t.psi*t.psi)
            pdot,_=t.tangent(self.x['H'])
            self.assertEqual(t.magnetic_dot(self.x['H']),2*t.coupling*t.psi*pdot)

    def test_gram_block_reconstruction(self):
        a,b,c=response_blocks(self.ts)
        M=response_matrix(self.ts)
        for i in range(6):
            for j in range(6):
                expected = a if i==j and i<3 else b if i==j else c if abs(i-j)==3 else Q(0)
                self.assertEqual(M[i][j],expected)
                self.assertEqual(M[i][j],M[j][i])

    def test_gram_det_two_multiplet_wedge(self):
        samples=((1,2,3,4),(2,5,-1,3),(0,1,1,0),(3,0,0,3),(0,1,0,2))
        for e1,b1,e2,b2 in samples:
            # Choose g=1 and psi integer so B_i = psi_i^2. General wedge
            # identity checked below by a direct 2x2 Gram determinant.
            expected=(e1*b2-e2*b1)**2
            d=(e1*e1+e2*e2)*(b1*b1+b2*b2)-(e1*b1+e2*b2)**2
            self.assertEqual(d,expected)
        self.assertEqual(det_exact(response_matrix(self.ts)),gram_det_formula(self.ts))
        self.assertEqual(gram_det_formula(self.ts),two_multiplet_wedge(self.ts)**6)

    def test_many_rational_gram_determinants(self):
        rng=Random(8808)
        for _ in range(140):
            ts=(Triad(Q(rng.randint(-3,3),6),Q(rng.randint(-5,5),7),Q(1,2)),
                Triad(Q(rng.randint(-3,3),5),Q(rng.randint(-5,5),6),Q(3,4)))
            self.assertEqual(det_exact(response_matrix(ts)),gram_det_formula(ts))
            self.assertEqual(gram_det_formula(ts),two_multiplet_wedge(ts)**6)
            self.assertGreaterEqual(gram_det_formula(ts),0)

    def test_single_multiplet_rank_deficiency(self):
        for e,psi in product((0,Q(1,2),Q(-3,5)),(0,Q(1,3),Q(-2,5))):
            t=Triad(psi,e,1)
            self.assertEqual(det_exact(response_matrix((t,))),0)

    def test_two_isotropic_electric_magnetic_full_rank(self):
        self.assertGreater(det_exact(response_matrix(self.ts)),0)
        self.assertNotEqual(two_multiplet_wedge(self.ts),0)

    def test_induced_positive_and_diagonal_match(self):
        r=self.x['theta']
        self.assertEqual(r['difference'],0)
        self.assertEqual(r['thetaEB'],0)
        self.assertGreater(r['thetaE'],0)
        self.assertEqual(r['inverseE'],r['inverseB'])
        self.assertEqual(r['inverseEB'],0)

    def test_mixed_block_is_inverse_mixed_response(self):
        ts=(Triad(Q(1,4),Q(1,8),1),Triad(Q(1,5),Q(1,7),1))
        r=induced_response(ts,1,Q(-1,20),Q(1,100),Q(3,50))
        self.assertNotEqual(r['thetaEB'],0)
        self.assertNotEqual(r['inverseEB'],0)
        self.assertEqual(r['inverseE']*r['inverseB']-r['inverseEB']**2,1/r['detBlock'])

    def test_matching_is_not_flow_invariant(self):
        me,mb,_=response_blocks(self.ts)
        _,_,mixdot=response_derivatives(self.ts,self.x['H'])
        self.assertEqual(mixdot,2*self.ts[0].coupling*self.ts[0].psi*(me-mb))
        self.assertEqual(self.x['alpha']*mixdot,
                         4*self.x['beta']*self.ts[0].coupling*self.ts[0].psi*self.x['Hdot'])
        self.assertNotEqual(mixdot,0)

    def test_nonzero_split_requires_mixed_dot(self):
        for psi in (Q(1,4),Q(2,5)):
            for e in (Q(0),Q(1,10),Q(1,3)):
                ts=(Triad(psi,e,1),Triad(psi,-e,1))
                me,mb,c=response_blocks(ts)
                self.assertEqual(c,0)
                _,_,mixed_rate=response_derivatives(ts,1)
                self.assertEqual(mixed_rate,2*psi*(me-mb))
                if me!=mb:
                    self.assertNotEqual(mixed_rate,0)

    def test_early_time_growth(self):
        dt=Q(1,10000)
        after=rk4_one_step(self.ts,self.x['H'],self.x['Hdot'],dt)
        c=response_blocks(after)[2]
        self.assertLess(c,0)
        self.assertLess(abs(c/dt-self.x['mixDot']),Q(1,1000))
        r=induced_response(after,self.x['H']+dt*self.x['Hdot'],self.x['Hdot'],
                           self.x['beta'],self.x['alpha'])
        self.assertNotEqual(r['thetaEB'],0)

    def test_YM_derivative_formula(self):
        rng=Random(42)
        for _ in range(80):
            e=Q(rng.randint(-3,3),7); psi=Q(rng.randint(-3,3),8)
            H=Q(rng.randint(-2,3),4);g=Q(2,3)
            t=Triad(psi,e,g)
            dme,dmb,dC=response_derivatives((t,),H)
            self.assertEqual(dC,-4*H*e*t.magnetic-2*g**3*psi**5+2*g*psi*e**2)
            self.assertEqual(dme,2*e*t.tangent(H)[1])
            self.assertEqual(dmb,2*t.magnetic*t.magnetic_dot(H))

    def test_negative_definite_domain_rejected(self):
        with self.assertRaises(ValueError): Triad(1,1,0)
        with self.assertRaises(ValueError): response_blocks(())
        with self.assertRaises(ValueError):induced_response(self.ts,10,10,1,1)
        with self.assertRaises(ValueError):rk4_one_step(self.ts,1,0,0)
        with self.assertRaises(ValueError):two_multiplet_wedge(self.ts[:1])

if __name__=='__main__':unittest.main()

class CoupledEinsteinYMLaboratory(unittest.TestCase):
    def test_initial_gr_and_response_matching(self):
        from research.toe.yang_mills_triads import instantaneous_gr_example
        x=instantaneous_gr_example()
        self.assertEqual(x['kappa'],Q(9,5))
        self.assertEqual(x['Lambda'],Q(3045,1024))
        self.assertEqual(x['matchDot'],0)
        self.assertNotEqual(x['thetaMixDot'],0)
        self.assertEqual(x['Hddot'],Q(9,128))

    def test_einstein_raychaudhuri_and_continuity(self):
        from research.toe.yang_mills_triads import einstein_ym_tangent
        x=symmetric_two_triad_example()
        for kappa in (Q(1),Q(9,5),Q(3,2)):
            dh,_=einstein_ym_tangent(x['triads'],x['H'],kappa)
            rho,p=energy_pressure(x['triads'])
            self.assertEqual(dh,-kappa*(rho+p)/2)
            self.assertEqual(energy_rate(x['triads'],x['H']),-4*x['H']*rho)

    def test_complete_gr_ym_flow_breaks_mixed_response(self):
        from research.toe.yang_mills_triads import (instantaneous_gr_example,
                                                      einstein_ym_rk4_one_step)
        x=instantaneous_gr_example()
        step=Q(1,10000)
        H1,ts1=einstein_ym_rk4_one_step(x['triads'],x['H'],x['kappa'],step)
        c1=response_blocks(ts1)[2]
        self.assertLess(c1,0)
        self.assertLess(abs(c1/step-x['mixDot']),Q(1,1000))
        from research.toe.yang_mills_triads import einstein_ym_lambda
        # RK4 conserves the GR Hamiltonian constraint to high order.
        self.assertLess(abs(einstein_ym_lambda(ts1,H1,x['kappa'])-x['Lambda']),Q(1,10**15))
        # Unlike the mixed block, the initial diagonal matching derivative is 0.
        from research.toe.yang_mills_triads import einstein_ym_tangent
        hdot1,_=einstein_ym_tangent(ts1,H1,x['kappa'])
        r1=induced_response(ts1,H1,hdot1,x['beta'],x['alpha'])
        self.assertNotEqual(r1['thetaEB'],0)
        self.assertLess(abs(r1['difference']),Q(1,10000000))

    def test_einstein_gr_consistency_parameter_errors(self):
        from research.toe.yang_mills_triads import einstein_ym_tangent,einstein_ym_rk4_one_step
        with self.assertRaises(ValueError):einstein_ym_tangent((Triad(1,0,1),),1,0)
        with self.assertRaises(ValueError):einstein_ym_rk4_one_step((Triad(1,0,1),),1,1,0)

class CurvatureResponseTests(unittest.TestCase):
    def test_full_six_by_six_riemann_pair_response(self):
        from research.toe.yang_mills_triads import raw_riemann_pair_response
        ts=(Triad(Q(1,4),Q(1,32),1),Triad(Q(1,4),-Q(1,32),1))
        M=raw_riemann_pair_response(ts,2)
        me,mb,c=response_blocks(ts)
        for i in range(6):
            for j in range(6):
                expected=2*(me if i==j and i<3 else mb if i==j else
                            -c if abs(i-j)==3 else Q(0))
                self.assertEqual(M[i][j],expected)
                self.assertEqual(M[i][j],M[j][i])
        self.assertEqual(det_exact(M),Q(2)**6*gram_det_formula(ts))

    def test_lorentzian_sign_of_mixed_curvature_response(self):
        from research.toe.yang_mills_triads import raw_riemann_pair_response
        t=Triad(Q(1,3),Q(1,6),Q(1,2))
        m=raw_riemann_pair_response((t,))
        self.assertEqual(m[0][3],-t.electric*t.magnetic)
        self.assertEqual(m[3][0],m[0][3])
        self.assertEqual(m[0][0],t.electric**2)
        self.assertEqual(m[3][3],t.magnetic**2)

    def test_zero_nonminimal_coupling_response(self):
        from research.toe.yang_mills_triads import raw_riemann_pair_response
        t=Triad(1,1,1)
        self.assertEqual(raw_riemann_pair_response((t,),0),tuple((Q(0),)*6 for _ in range(6)))

class FixtureTests(unittest.TestCase):
    def test_source_scoped_reference_fixture(self):
        import json
        from pathlib import Path
        from research.toe.yang_mills_triads import reference_experiment
        path=Path(__file__).resolve().parent.parent/'research/toe/fixtures/yang_mills_two_triad_synthetic.json'
        self.assertEqual(json.loads(path.read_text()),reference_experiment())
        self.assertEqual(reference_experiment()['initial']['diagonalMatchDot'],'0')
        self.assertEqual(reference_experiment()['initial']['thetaMixedDot'],'-9/51200')
