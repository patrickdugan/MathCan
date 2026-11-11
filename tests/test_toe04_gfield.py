"""TOE-04: source-anchored flat-vacuum ΛGfE, synthetic branch only."""
import json
import math
import random
from pathlib import Path
from fractions import Fraction
import unittest

from research.toe.gfield_flrw import (
    SECTORS, DomainError, acceleration, curvature_polynomial, curvature_scalars,
    de_sitter_lambda, eigenvalues, evolve_redshift, fluid_eigenvalues,
    hessian_direction, invariant, lambda_g, reference_experiment,
    vacuum_lapse_constraint,
)
from research.toe.bianconi_profile import frw_design, profile, synthetic_covariance


class GFieldCurvatureTests(unittest.TestCase):
    def test_degeneracies_and_gr_linear_coefficient(self):
        self.assertEqual([row[3] for row in SECTORS], [1,1,3,3,3])
        self.assertEqual(sum(w for _,_,_,w in SECTORS),11)
        self.assertEqual(sum(w*a for _,a,_,w in SECTORS),18)
        self.assertEqual(sum(w*b for _,_,b,w in SECTORS),18)

    def test_vacuum_gfield_inversion(self):
        A,B = curvature_scalars(1, -0.01)
        rows = eigenvalues(A,B,.02)
        for _,mult,u,G in rows:
            self.assertGreater(mult,0)
            self.assertGreater(G,0)
            self.assertAlmostEqual(G*(1-u),1,places=14)
        self.assertGreater(lambda_g(A,B,.02),0)

    def test_matter_eigenvalues_are_algebraic_only(self):
        pure = eigenvalues(1, 1, .01)
        self.assertEqual(fluid_eigenvalues(1,1,.01,0,0),pure)
        dust = fluid_eigenvalues(1,1,.01,Fraction(2,100),0)
        self.assertAlmostEqual(dust[1][2]-pure[1][2],3*.02/8)
        self.assertAlmostEqual(dust[2][2]-pure[2][2],-.02/8)
        for i in (0,3,4):self.assertEqual(dust[i],pure[i])

    def test_curvature_quadratic_identity(self):
        rnd=random.Random(516)
        for a,b in [(0,0),(1,2),(-4,7)]+[(rnd.randint(-15,15),rnd.randint(-15,15)) for _ in range(130)]:
            v=curvature_polynomial(a,b)
            self.assertEqual(v['flattened_quad'],v['R']**2+v['Ricci2']+v['Riemann2'])
            self.assertEqual(v['flattened_quad'],5*v['Ricci2']+v['GaussBonnet'])

    def test_strict_convexity_and_positive_hessian(self):
        for A,B in [(1,1),(.25,1),(1,-.1),(-.5,.5)]:
            _,_,_,faa,fab,fbb=invariant(A,B,.01)
            self.assertGreater(faa,0)
            self.assertGreater(fbb,0)
            self.assertGreater(faa*fbb-fab*fab,0)
            for x,y in ((1,0),(0,1),(3,-5),(.2,.8)):
                self.assertGreater(hessian_direction(A,B,.01,x,y),0)
                self.assertAlmostEqual(hessian_direction(A,B,.01,x,y),
                                       faa*x*x+2*fab*x*y+fbb*y*y,places=12)

    def test_derivatives_against_finite_differences(self):
        A,B,b=.92,1.04,.015
        f,fa,fb,faa,fab,fbb=invariant(A,B,b)
        h=1e-5
        fp=invariant(A+h,B,b)
        fm=invariant(A-h,B,b)
        self.assertAlmostEqual((fp[0]-fm[0])/(2*h),fa,delta=1e-8)
        self.assertAlmostEqual((fp[1]-fm[1])/(2*h),faa,delta=1e-7)
        self.assertAlmostEqual((fp[2]-fm[2])/(2*h),fab,delta=1e-7)

    def test_gfield_domain_checks(self):
        with self.assertRaises(DomainError):eigenvalues(1,1,.1)
        with self.assertRaises(DomainError):eigenvalues(1,1,.02,matter_time=-2)
        with self.assertRaises(ValueError):invariant(1,1,0)
        with self.assertRaises(ValueError):eigenvalues(float('nan'),1,.02)


class ReducedVacuumTests(unittest.TestCase):
    def test_de_sitter_calibration(self):
        for b in (.001,.01,.02,.04):
            l=de_sitter_lambda(1,b)
            self.assertGreater(l,0)
            self.assertAlmostEqual(vacuum_lapse_constraint(1,0,0,b,l),0,delta=1e-13)
            self.assertAlmostEqual(acceleration(1,0,b,l),0,delta=1e-11)

    def test_de_sitter_first_correction_is_quadratic_in_beta(self):
        # From the five sector logarithms: Lambda_dS=3 - 157/3*b^2 + O(b^3).
        b=1e-4
        observed=(3-de_sitter_lambda(1,b))/(b*b)
        self.assertAlmostEqual(observed,157/3,delta=.2)

    def test_weak_field_matches_gr_friedmann(self):
        for h,q,j,l in ((1.02,-.05,.1,3),(.9,.05,-.02,2.4)):
            b=1e-7
            value=vacuum_lapse_constraint(h,q,j,b,l)/(6*b)
            self.assertAlmostEqual(value,3*h*h-l,delta=3e-6)

    def test_unique_acceleration_is_actual_constraint_root(self):
        for h,q,b,l in ((1,-.01,.02,3),(1.02,.03,.015,3.1),(.8,.1,.004,1.9)):
            j=acceleration(h,q,b,l)
            self.assertAlmostEqual(vacuum_lapse_constraint(h,q,j,b,l),0,delta=1e-12)
            self.assertNotAlmostEqual(vacuum_lapse_constraint(h,q,j+.01,b,l),0,delta=1e-8)

    def test_de_sitter_curve_flat_and_positive_g(self):
        b=.02
        curve=evolve_redshift([0,.2,.4,.6,.8,1.0,1.2],beta=b,Lambda=de_sitter_lambda(1,b))
        for r in curve:
            self.assertAlmostEqual(r['H'],1,delta=1e-11)
            self.assertAlmostEqual(r['Hdot'],0,delta=1e-11)
            self.assertGreater(r['G_min'],0)
            self.assertLess(abs(r['constraint_residual']),1e-12)

    def test_nonde_sitter_solution_convergence(self):
        b=.02;l=de_sitter_lambda(1,b)
        a=evolve_redshift([0,1.2],beta=b,Lambda=l,Hdot0=-.01,max_step=.005)
        c=evolve_redshift([0,1.2],beta=b,Lambda=l,Hdot0=-.01,max_step=.001)
        self.assertAlmostEqual(a[-1]['H'],c[-1]['H'],delta=5e-9)
        self.assertAlmostEqual(a[-1]['Hdot'],c[-1]['Hdot'],delta=5e-9)
        self.assertAlmostEqual(c[-1]['H'],.9990942622187,delta=2e-10)
        self.assertTrue(all(r['G_min']>0 for r in c))

    def test_curvature_energy_on_branch(self):
        b=.02
        curve=evolve_redshift([0,.4,.8,1.2],beta=b,Lambda=de_sitter_lambda(1,b),Hdot0=-.01)
        self.assertTrue(all(r['lambda_G']>0 for r in curve))
        self.assertGreater(abs(curve[0]['lambda_G']-curve[-1]['lambda_G']),1e-3)
        self.assertTrue(all(abs(r['constraint_residual'])<1e-12 for r in curve))

    def test_friedmann_profile_on_synthetic_vacuum_curve(self):
        b=.02
        z=[Fraction(i,5) for i in range(7)]
        curve=evolve_redshift(z,beta=b,Lambda=de_sitter_lambda(1,b),Hdot0=-.01)
        observed=tuple(Fraction(f'{r["H"]**2:.12f}') for r in curve)
        fit=profile(observed,frw_design(z),synthetic_covariance(z))
        self.assertGreater(fit['chi2'],0)
        self.assertAlmostEqual(float(fit['chi2']),.00025170188459,delta=2e-8)

    def test_invalid_grid_and_expansion(self):
        b=.02;l=de_sitter_lambda(1,b)
        for z in ([],[.1],[0,.4,.4],[0,.6,.4],[0,-.2]):
            with self.assertRaises(ValueError):evolve_redshift(z,beta=b,Lambda=l)
        with self.assertRaises(ValueError):evolve_redshift([0,1],beta=b,Lambda=l,H0=0)
        with self.assertRaises(ValueError):evolve_redshift([0,1],beta=b,Lambda=l,max_step=0)

    def test_machine_receipt(self):
        fixture=Path(__file__).resolve().parent.parent/'research/toe/fixtures/gfield_vacuum_synthetic.json'
        expected=json.loads(fixture.read_text())
        new=reference_experiment()
        self.assertEqual(new['schema'],expected['schema'])
        self.assertEqual(new['H'],expected['H'])
        self.assertEqual(new['G_min'],expected['G_min'])
        self.assertLess(new['max_abs_constraint_residual'],1e-12)
        self.assertEqual(new['evidence'],"synthetic; no matter-coupled or observed H(z)")

if __name__ == '__main__':unittest.main()
