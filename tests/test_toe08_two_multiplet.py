"""TOE-08B two-triad exact-rational source and flavor-area checks."""
from fractions import Fraction as F
from itertools import product
from random import Random
import unittest
from research.toe.twoform_multiplets import (
    TwoTriadState,invariants,rhs,invariant_derivatives,lagrange_gap,
    radial_certificate,cone_gap,total_stress,spectator_powerlaw,
)
from research.toe.twoform_triad import stress


class TwoMultipletTests(unittest.TestCase):
    def test_lagrange_identity_exhaustive(self):
        for components in product((-1,0,1),repeat=4):
            s=TwoTriadState(*components)
            self.assertEqual(lagrange_gap(s),0)

    def test_invariant_derivatives_central_difference_symbolic(self):
        rng=Random(80605)
        for _ in range(500):
            vals=[F(rng.randint(-5,5),rng.randint(1,7)) for _ in range(4)]
            s=TwoTriadState(*vals)
            H=F(rng.randint(1,5),8);D=F(rng.randint(-4,4),9)
            m1=F(rng.randint(0,6),7);m2=F(rng.randint(0,6),7)
            l1=F(rng.randint(-4,4),17);l2=F(rng.randint(-4,4),17)
            d=invariant_derivatives(H,D,s,m1,l1,m2,l2)
            sd=rhs(H,s,m1,l1,m2,l2)
            b1,b2,v1,v2=s.b1,s.b2,s.v1,s.v2
            x1,x2,y1,y2=sd
            self.assertEqual(d['Sdot'],2*(b1*x1+b2*x2))
            self.assertEqual(d['Qdot'],x1*v1+x2*v2+b1*y1+b2*y2)
            self.assertEqual(d['Wdot'],x1*v2+b1*y2-x2*v1-b2*y1)
            self.assertEqual(d['Sddot'],2*(x1*x1+x2*x2+b1*(y1-2*D*b1-2*H*x1)+b2*(y2-2*D*b2-2*H*x2)))

    def test_exact_radial_certificate_500_states(self):
        rng=Random(80612)
        verified=0
        for _ in range(500):
            s=TwoTriadState(*(F(rng.randint(-8,8),11) for i in range(4)))
            if not invariants(s)[0]:continue
            H=F(rng.randint(1,20),17);D=F(rng.randint(-8,8),23)
            m1=F(rng.randint(0,5),7);m2=F(rng.randint(0,5),9)
            l1=F(rng.randint(-3,3),11);l2=F(rng.randint(-3,3),13)
            d=radial_certificate(H,D,s,m1,l1,m2,l2)
            self.assertEqual(d['lhs'],d['rhs'])
            self.assertEqual(d['gap'],0)
            self.assertGreaterEqual(d['flavor_term'],0)
            verified+=1
        self.assertGreater(verified,490)

    def test_zero_response_fails_closed(self):
        with self.assertRaises(ValueError):radial_certificate(1,0,TwoTriadState(0,0,1,1))

    def test_equal_coupling_wronskian_redshifts(self):
        s=TwoTriadState(1,F(1,3),F(2),F(-1,4))
        for h in (F(1),F(4,3),F(0)):
            d=invariant_derivatives(h,F(-1,10),s,F(1,2),F(1,8),F(1,2),F(1,8))
            self.assertEqual(d['Wdot'],-3*h*d['W'])

    def test_mismatch_wronskian_source(self):
        s=TwoTriadState(2,3,1,5)
        h=F(1,2);d=invariant_derivatives(h,0,s,1,F(1,2),3,0)
        M1=F(1)-2*F(1,2)*h*h;M2=F(3)
        self.assertEqual(d['Wdot']+3*h*d['W'],(M1-M2)*6)

    def test_flavor_rotation_same_amplitude_changes_cone_future(self):
        s0=TwoTriadState(1,0,3,F(1,2))
        self.assertEqual(cone_gap(F(1,100),F(1,25),1,F(-2),s0),0)
        matched=spectator_powerlaw(2,TwoTriadState(1,0,3,0),steps=400)
        rotating=spectator_powerlaw(2,s0,steps=400)
        self.assertAlmostEqual(matched['S'],F(1,4),places=8)
        self.assertGreater(rotating['S'],.25)
        self.assertAlmostEqual(rotating['W'],.5/64,places=8)
        self.assertAlmostEqual(rotating['b2'],7/96,places=8)
        self.assertGreater(rotating['S']-matched['S'],.005)

    def test_matching_necessity_and_sum_response(self):
        s=TwoTriadState(1,2,0,0)
        beta=F(1,100);alpha=F(1,20);chi=F(2,5)
        Hdot=-alpha*chi*F(5)/(2*beta)
        self.assertEqual(cone_gap(beta,alpha,chi,Hdot,s),0)
        self.assertNotEqual(cone_gap(beta,alpha,chi,Hdot+F(1,10),s),0)

    def test_stress_additive_two_actions(self):
        for H,D,b1,b2 in product((F(1),F(2)),(F(-1,4),F(0)),(F(0),F(2,3)),(F(-1,3),F(1))):
            s=TwoTriadState(b1,b2,2,3)
            tot=total_stress(H,D,s,F(1,2),F(1,4),F(3,5),F(-1,6))
            a=stress(H,D,b1,2,F(1,2),F(1,4))
            b=stress(H,D,b2,3,F(3,5),F(-1,6))
            self.assertEqual(tot,(a.rho+b.rho,a.pressure+b.pressure))

    def test_invalid_couplings(self):
        s=TwoTriadState(1,1,1,1)
        with self.assertRaises(ValueError):cone_gap(0,1,1,-1,s)
        with self.assertRaises(ValueError):rhs(1,s,m2_1=-1)
        with self.assertRaises(ValueError):spectator_powerlaw(2,s,t0=2,t1=1)


class TwoMultipletAnalyticTests(unittest.TestCase):
    def test_powerlaw_closed_form_solves_both_fields(self):
        from research.toe.twoform_multiplets import exact_powerlaw_twofield
        for t in (F(1),F(6,5),F(3,2),F(2),F(3)):
            s=exact_powerlaw_twofield(t)
            H=2/t
            # b1',b2',v1',v2' from the analytic formulas
            derivative=(
                -1/t**2,
                F(-1,6)/t**2 + F(2,3)/t**5,
                -6/t**3,
                -1/t**3,
            )
            self.assertEqual(rhs(H,s),derivative)
            self.assertEqual(lagrange_gap(s),0)
            if t>1:self.assertGreater(invariants(s)[0],1/t**2)
            else:self.assertEqual(invariants(s)[0],1/t**2)

    def test_exact_flavor_counterexample_at_t2(self):
        from research.toe.twoform_multiplets import exact_powerlaw_twofield
        s=exact_powerlaw_twofield(F(2))
        self.assertEqual(s.b1,F(1,2))
        self.assertEqual(s.b2,F(7,96))
        S,Q,W=invariants(s)
        self.assertEqual(S-F(1,4),F(49,9216))
        self.assertEqual(W,F(1,128))
        # S target = -2*beta*hdot/(alpha*chi), beta=1/100,
        # alpha=1/25, chi=1 and hdot=-2/t²: at t=2 S_target=1/4.
        self.assertNotEqual(cone_gap(F(1,100),F(1,25),1,F(-1,2),s),0)

    def test_homogeneous_kinetic_degeneracy(self):
        from research.toe.twoform_multiplets import homogeneous_two_kinetic
        for a,N,w1,w2 in product((F(1),F(2)),(F(1),F(3,2)),(F(0),F(1),F(3)),(F(-1),F(0),F(2))):
            lam1=F(1,2);lam2=F(1,3)
            mp2=(lam1*w1*w1+lam2*w2*w2)/(a**4)
            K=homogeneous_two_kinetic(a,N,w1,w2,lam1,lam2,mp2)
            self.assertEqual(K[0][0],0)
            self.assertEqual(K[1][1],F(3)/(N*a))
            self.assertEqual(K[2][2],F(3)/(N*a))
            self.assertEqual(K[0][1],0)

    def test_homogeneous_eh_sign_gates(self):
        from research.toe.twoform_multiplets import homogeneous_two_kinetic
        for bound in (F(0),F(1,2),F(1)):
            K=homogeneous_two_kinetic(2,1,4,0,F(1,4),0,bound)
            self.assertEqual(K[0][0],12*(F(1,4)-bound))


if __name__ == '__main__': unittest.main()
