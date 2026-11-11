"""TOE-04: source-anchored FLRW sector tests, entirely synthetic."""
import math
import random
import unittest
from fractions import Fraction as F

from research.toe.gfield_flrw import (
    SECTORS,DomainError,curvature_scalars,eigenvalues,fluid_eigenvalues,
    invariant,hessian_direction,lambda_g,de_sitter_lambda,
    vacuum_lapse_constraint,acceleration,evolve_redshift,
    curvature_polynomial,reference_experiment,
)
from research.toe.bianconi_profile import frw_design, profile, synthetic_covariance

class GFieldSpectrumTests(unittest.TestCase):
    def test_multiplicity_and_linear_GR_trace(self):
        self.assertEqual(tuple(w for _,_,_,w in SECTORS),(1,1,3,3,3))
        self.assertEqual(sum(w for _,_,_,w in SECTORS),11)
        self.assertEqual(sum(w*a for _,a,_,w in SECTORS),18)
        self.assertEqual(sum(w*b for _,_,b,w in SECTORS),18)

    def test_eigenvalue_inversion_and_energy(self):
        a,b=curvature_scalars(1,-.01)
        for _,mult,u,g in eigenvalues(a,b,.02):
            self.assertGreater(mult,0)
            self.assertGreater(g,0)
            self.assertAlmostEqual(g*(1-u),1,delta=1e-13)
        self.assertGreater(lambda_g(a,b,.02),0)

    def test_fluid_only_algebraic(self):
        base=eigenvalues(1,1,.01)
        dust=fluid_eigenvalues(1,1,.01,F(1,50),0)
        self.assertEqual(fluid_eigenvalues(1,1,.01,0,0),base)
        self.assertAlmostEqual(dust[1][2]-base[1][2],3*.02/8)
        self.assertAlmostEqual(dust[2][2]-base[2][2],-.02/8)
        for i in (0,3,4):self.assertEqual(dust[i],base[i])

    def test_curvature_polynomial_identity(self):
        rnd=random.Random(516)
        for a,b in [(0,0),(1,2)]+[(rnd.randint(-15,15),rnd.randint(-15,15)) for _ in range(100)]:
            c=curvature_polynomial(a,b)
            self.assertEqual(c["flattened_quad"],c["R"]**2+c["Ricci2"]+c["Riemann2"])
            self.assertEqual(c["flattened_quad"],5*c["Ricci2"]+c["GaussBonnet"])

    def test_positive_curvature_hessian(self):
        for a,b in ((1,1),(.25,1),(1,-.1),(-.5,.5)):
            _,_,_,faa,fab,fbb=invariant(a,b,.01)
            self.assertGreater(faa*fbb-fab*fab,0)
            for x,y in ((1,0),(0,1),(3,-5),(.2,.8)):
                self.assertGreater(hessian_direction(a,b,.01,x,y),0)
                self.assertAlmostEqual(hessian_direction(a,b,.01,x,y),
                                       faa*x*x+2*fab*x*y+fbb*y*y,delta=1e-10)

    def test_analytic_partials(self):
        a,b,beta=.92,1.04,.015
        f,fa,fb,faa,fab,_=invariant(a,b,beta)
        h=1e-5
        p=invariant(a+h,b,beta)
        m=invariant(a-h,b,beta)
        self.assertAlmostEqual((p[0]-m[0])/(2*h),fa,delta=1e-8)
        self.assertAlmostEqual((p[1]-m[1])/(2*h),faa,delta=1e-7)
        self.assertAlmostEqual((p[2]-m[2])/(2*h),fab,delta=1e-7)

    def test_positive_domain_failures(self):
        with self.assertRaises(DomainError):eigenvalues(1,1,.1)
        with self.assertRaises(DomainError):eigenvalues(1,1,.02,matter_time=-2)
        with self.assertRaises(ValueError):eigenvalues(float("nan"),1,.02)
        with self.assertRaises(ValueError):invariant(1,1,0)

class VacuumEvolutionTests(unittest.TestCase):
    def test_de_sitter_constraint(self):
        for beta in (.001,.01,.02,.04):
            l=de_sitter_lambda(1,beta)
            self.assertGreater(l,0)
            self.assertAlmostEqual(vacuum_lapse_constraint(1,0,0,beta,l),0,delta=1e-13)
            self.assertAlmostEqual(acceleration(1,0,beta,l),0,delta=1e-11)

    def test_de_sitter_small_beta_coefficient(self):
        beta=1e-4
        self.assertAlmostEqual((3-de_sitter_lambda(1,beta))/beta**2,157/3,delta=.2)

    def test_GR_constraint_limit(self):
        for h,q,j,l in ((1.02,-.05,.1,3),(.9,.05,-.02,2.4)):
            beta=1e-7
            c=vacuum_lapse_constraint(h,q,j,beta,l)/(6*beta)
            self.assertAlmostEqual(c,3*h*h-l,delta=3e-6)

    def test_acceleration_solves_lapse_equation(self):
        for h,q,b,l in ((1,-.01,.02,3),(1.02,.03,.015,3.1),(.8,.1,.004,1.9)):
            j=acceleration(h,q,b,l)
            self.assertAlmostEqual(vacuum_lapse_constraint(h,q,j,b,l),0,delta=1e-12)
            self.assertGreater(abs(vacuum_lapse_constraint(h,q,j+.01,b,l)),1e-8)

    def test_de_sitter_Hz(self):
        b=.02
        curve=evolve_redshift([0,.2,.4,.6,.8,1,1.2],beta=b,Lambda=de_sitter_lambda(1,b))
        self.assertTrue(all(abs(r["H"]-1)<1e-11 for r in curve))
        self.assertTrue(all(abs(r["Hdot"])<1e-11 for r in curve))

    def test_rk4_step_convergence(self):
        b=.02;l=de_sitter_lambda(1,b)
        a=evolve_redshift([0,1.2],beta=b,Lambda=l,Hdot0=-.01,max_step=.005)
        c=evolve_redshift([0,1.2],beta=b,Lambda=l,Hdot0=-.01,max_step=.001)
        self.assertAlmostEqual(a[-1]["H"],c[-1]["H"],delta=5e-9)
        self.assertAlmostEqual(a[-1]["Hdot"],c[-1]["Hdot"],delta=5e-9)
        self.assertAlmostEqual(c[-1]["H"],.9990942622187,delta=2e-10)
        self.assertTrue(all(r["G_min"]>0 for r in c))

    def test_emergent_energy_and_lapse_residual(self):
        b=.02;l=de_sitter_lambda(1,b)
        curve=evolve_redshift([0,.4,.8,1.2],beta=b,Lambda=l,Hdot0=-.01)
        self.assertTrue(all(r["lambda_G"]>0 for r in curve))
        self.assertGreater(abs(curve[0]["lambda_G"]-curve[-1]["lambda_G"]),.001)
        self.assertTrue(all(abs(r["constraint_residual"])<1e-12 for r in curve))

    def test_synthetic_FRW_profile(self):
        z=tuple(F(i,5) for i in range(7))
        b=.02;l=de_sitter_lambda(1,b)
        curve=evolve_redshift(z,beta=b,Lambda=l,Hdot0=-.01)
        y=tuple(F(f'{r["H"]**2:.12f}') for r in curve)
        fit=profile(y,frw_design(z),synthetic_covariance(z))
        self.assertGreater(fit["chi2"],0)
        self.assertAlmostEqual(float(fit["chi2"]),.00025170188459,delta=2e-8)

    def test_input_validation(self):
        b=.02;l=de_sitter_lambda(1,b)
        for zs in ([],[.1],[0,.4,.4],[0,.6,.4],[0,-.2]):
            with self.assertRaises(ValueError):evolve_redshift(zs,beta=b,Lambda=l)
        with self.assertRaises(ValueError):evolve_redshift([0,1],beta=b,Lambda=l,H0=0)
        with self.assertRaises(ValueError):evolve_redshift([0,1],beta=b,Lambda=l,max_step=0)

    def test_reference_receipt(self):
        r=reference_experiment()
        self.assertEqual(r["schema"],"mathcan.toe04.v1")
        self.assertEqual(len(r["H"]),7)
        self.assertAlmostEqual(r["H"][3],1.004538089586,delta=2e-10)
        self.assertAlmostEqual(r["profiled_synthetic_chi2"],.00025170188459,delta=2e-8)
        self.assertLess(r["max_abs_constraint_residual"],1e-12)
        self.assertIn("synthetic",r["evidence"])

if __name__=="__main__":unittest.main()
