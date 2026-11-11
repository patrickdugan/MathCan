"""TOE-05 source-derived conditional scalar/metric equations and exact oracles."""
import math
import random
import unittest
from fractions import Fraction as F

from research.toe.gfield_scalar_flrw import (
    ScalarModel, DomainError, SECTORS, WEIGHTS, rational_determinant,
    reference_experiment, tracefree_flrw,
)
from research.toe.gfield_flrw import acceleration as vacuum_acceleration, de_sitter_lambda


class DressedScalarTests(unittest.TestCase):
    def setUp(self):
        self.m=ScalarModel(beta=.01, alpha=.06, mass=.4, Lambda=2.98)
        self.s=(1., -.01, .2, -.1)

    def test_source_multiplicities(self):
        self.assertEqual(sum(WEIGHTS),11)
        self.assertEqual(len(SECTORS),5)

    def test_induced_metric_eigenvalues(self):
        ds=self.m.spectral(*self.s)
        H,q,phi,pi=self.s
        A=H*H+q
        B=H*H
        self.assertAlmostEqual(ds[0],1+self.m.alpha*self.m.mass**2*phi**2-6*self.m.beta*(A+B))
        self.assertAlmostEqual(ds[1],1-self.m.alpha*pi*pi-3*self.m.beta*A)
        self.assertTrue(all(v>0 for v in ds))

    def test_negative_induced_metric_fail_closed(self):
        for sample in ((4.,0.,0.,0.),(1.,0.,0.,10.)):
            with self.assertRaises(DomainError): self.m.spectral(*sample)

    def test_non_expanding_branch_rejected(self):
        with self.assertRaises(DomainError): self.m.rhs(0.,0.,0.,0.)

    def test_invalid_couplings(self):
        for beta,alpha in ((0,.1),(.1,0),(-1,1),(1,-1)):
            with self.assertRaises(ValueError): ScalarModel(beta,alpha,.4,0)

    def test_gradient_against_central_differences(self):
        H,q,phi,pi=self.s
        p=self.m.partials(*self.s)
        eps=1e-6
        f=lambda h,z,x,v:self.m.partials(h,z,x,v)["f"]
        self.assertAlmostEqual((f(H,q+eps,phi,pi)-f(H,q-eps,phi,pi))/(2*eps),p["fa"],places=8)
        self.assertAlmostEqual((f(H,q,phi+eps,pi)-f(H,q,phi-eps,pi))/(2*eps),p["fphi"],places=8)
        self.assertAlmostEqual((f(H,q,phi,pi+eps)-f(H,q,phi,pi-eps))/(2*eps),p["fpi"],places=8)

    def test_hessian_against_central_differences(self):
        H,q,phi,pi=self.s
        p=self.m.partials(*self.s)
        eps=2e-6
        fa=lambda z,x,v:self.m.partials(H,z,x,v)["fa"]
        self.assertAlmostEqual((fa(q+eps,phi,pi)-fa(q-eps,phi,pi))/(2*eps),p["faa"],places=8)
        self.assertAlmostEqual((fa(q,phi,pi+eps)-fa(q,phi,pi-eps))/(2*eps),p["fapi"],places=8)
        self.assertAlmostEqual((fa(q,phi+eps,pi)-fa(q,phi-eps,pi))/(2*eps),p["faphi"],places=8)

    def test_rational_schur_positive_exhaustive(self):
        # 300 rational states, all in the positive G-field domain.
        rng=random.Random(20261111)
        for _ in range(300):
            A=F(rng.randint(-4,5),10)
            B=F(rng.randint(0,6),10)
            phi=F(rng.randint(-5,5),10)
            pi=F(rng.randint(-5,5),10)
            r=rational_determinant(F(1,100),F(3,50),F(4,25),A,B,phi,pi)
            self.assertEqual(r["direct"],r["decomposed"])
            self.assertGreater(r["peripheral"],0)

    def test_schur_float_decomposition(self):
        r=self.m.determinant_certificate(*self.s)
        self.assertTrue(r["positive"])
        self.assertAlmostEqual(r["direct"],r["decomposed"],places=12)

    def test_lapse_and_scalar_el_solved_together(self):
        _,j,_,pd=self.m.rhs(*self.s)
        lapse,scalar=self.m.residuals(*self.s,j,pd)
        self.assertLess(abs(lapse),1e-12)
        self.assertLess(abs(scalar),1e-12)

    def test_scalar_equation_mixed_derivative_matters(self):
        _,j,_,pd=self.m.rhs(*self.s)
        # Independently evaluating the scalar equation using d/dt(pi/theta_t)
        H,q,phi,pi=self.s
        d0,d1,*_=self.m.spectral(*self.s)
        d1dot=-2*self.m.alpha*pi*pd-3*self.m.beta*(j+2*H*q)
        lhs=(pd*d1-pi*d1dot)/d1**2+3*H*pi/d1+self.m.mass**2*phi/d0
        self.assertLess(abs(lhs),1e-12)

    def test_bare_exchange_identity(self):
        for s in (self.s,(1.03,-.03,-.1,.12),(1.05,.01,.25,.09)):
            _,j,_,pd=self.m.rhs(*s)
            a,b=self.m.scalar_bare_exchange(*s,j,pd)
            self.assertAlmostEqual(a,b,places=12)

    def test_scalar_zero_is_exact_vacuum_branch(self):
        b=.02
        lam=de_sitter_lambda(1.,b)
        m=ScalarModel(b, 6*b,.3,lam)
        _,j,_,pd=m.rhs(1.,0.,0.,0.)
        self.assertAlmostEqual(j,0.,places=11)
        self.assertAlmostEqual(pd,0.,places=11)
        self.assertAlmostEqual(j,vacuum_acceleration(1.,0.,b,lam),places=10)

    def test_general_vacuum_matches_toe04(self):
        b=.02
        lam=de_sitter_lambda(1.,b)
        m=ScalarModel(b,6*b,.6,lam)
        for q in (-.03,0.,.02):
            _,j,_,pd=m.rhs(1.,q,0.,0.)
            self.assertAlmostEqual(j,vacuum_acceleration(1.,q,b,lam),places=10)
            self.assertAlmostEqual(pd,0.)

    def test_gr_limit_scalar_and_lapse(self):
        H,q,phi,pi=(1.,-.01,.2,-.1)
        beta=1.e-7
        alpha=6*beta
        model=ScalarModel(beta,alpha,.4,3.)
        p=model.partials(H,q,phi,pi)
        # This leading constraint includes the constant cosmological term.
        j,pd=.05,.25
        lhs=model.residuals(H,q,phi,pi,j,pd)[0]/(6*beta)
        expected=3*H**2-3.-(pi*pi+model.mass**2*phi**2)
        self.assertAlmostEqual(lhs,expected,places=5)
        # E-L divided by 2 alpha reduces to KG in the weak-curvature limit.
        scalar=model.residuals(H,q,phi,pi,j,pd)[1]/(2*alpha)
        self.assertAlmostEqual(scalar,pd+3*H*pi+model.mass**2*phi,places=5)

    def test_initial_lambda_calibration(self):
        H,q,phi,pi=self.s
        kgdot=-3*H*pi-self.m.mass**2*phi
        j=-2*self.m.kappa*pi*kgdot
        lam,pidot=self.m.lambda_for_initial_acceleration(*self.s,j)
        model=ScalarModel(self.m.beta,self.m.alpha,self.m.mass,lam)
        _,jj,_,pp=model.rhs(*self.s)
        self.assertAlmostEqual(jj,j,places=10)
        self.assertAlmostEqual(pp,pidot,places=10)

    def test_evolution_step_convergence(self):
        lam,_=self.m.lambda_for_initial_acceleration(*self.s,.0536)
        m=ScalarModel(.01,.06,.4,lam)
        zz=(0.,.1,.2,.3,.4)
        a=m.evolve(zz,H0=1,Hdot0=-.01,phi0=.2,pi0=-.1,max_step=.001)
        b=m.evolve(zz,H0=1,Hdot0=-.01,phi0=.2,pi0=-.1,max_step=.0005)
        for x,y in zip(a,b):
            self.assertAlmostEqual(x["H"],y["H"],places=8)
            self.assertAlmostEqual(x["phi"],y["phi"],places=8)
            self.assertTrue(all(g>0 for g in x["G"]))
            self.assertLess(abs(x["constraint_residual"]),1e-12)
            self.assertLess(abs(x["scalar_residual"]),1e-12)

    def test_field_sign_symmetry(self):
        lam,_=self.m.lambda_for_initial_acceleration(*self.s,.0536)
        m=ScalarModel(.01,.06,.4,lam)
        a=m.evolve((0.,.2,.4),H0=1,Hdot0=-.01,phi0=.2,pi0=-.1,max_step=.001)
        b=m.evolve((0.,.2,.4),H0=1,Hdot0=-.01,phi0=-.2,pi0=.1,max_step=.001)
        for x,y in zip(a,b):
            self.assertAlmostEqual(x["H"],y["H"],places=12)
            self.assertAlmostEqual(x["phi"],-y["phi"],places=12)
            self.assertAlmostEqual(x["phidot"],-y["phidot"],places=12)

    def test_tracefree_vacuum_shift_and_soundness(self):
        k=F(1,5)
        x0,xs=F(1,2),F(5,2)
        rho,p=F(2),F(3)
        r=tracefree_flrw(x0,xs,rho,p,k)
        self.assertEqual(r,0)
        for v in (F(1),F(-3,4),F(999)):
            self.assertEqual(tracefree_flrw(x0,xs,rho+v,p-v,k),r)
        self.assertNotEqual(tracefree_flrw(x0,xs,rho+F(1),p,k),r)

    def test_reference_fixture(self):
        r=reference_experiment()
        self.assertEqual(r["schema"],"mathcan.toe05.scalar.v1")
        self.assertEqual(len(r["curve"]),6)
        self.assertTrue(r["max_lapse_residual"]<1e-12)
        self.assertTrue(r["max_scalar_residual"]<1e-12)


if __name__ == '__main__':
    unittest.main()
