"""TOE-06 exact geometric gates, conditional TT checks, reduced spatial E-L."""
from dataclasses import replace
from fractions import Fraction as F
import math
import random
import unittest

from research.toe.gfield_scalar_flrw import ScalarModel, reference_experiment
from research.toe.gfield_flrw import de_sitter_lambda
from research.toe.covariant_tensors import (
    flrw_ricci, responses, tt_symbol, tt_symbol_at, tt_gate,
    gfield_curvature_trace, CovariantComponents,
    covariant_equation_residuals, spatial_minisuperspace_residual, reference_audit,
)

class RicciAndTensorTests(unittest.TestCase):
    def test_flat_sourced_ricci(self):
        r=flrw_ricci(1,F(-1,100))
        self.assertEqual(r['R00'],F(-297,100))
        self.assertEqual(r['R'],F(1194,100))
        self.assertEqual(r['tracefree_Ricci_sq'],F(3,10000))

    def test_spatial_curvature_einstein_locus(self):
        for x in (F(-2,5),F(0),F(1,3)):
            r=flrw_ricci(F(2),x,x)
            self.assertTrue(r['Einstein_locus'])
            self.assertEqual(r['TF00'],0)
            self.assertEqual(r['TFs'],0)

    def test_ricci_trace_independent_grid(self):
        rng=random.Random(2026111106)
        for _ in range(500):
            H=F(rng.randint(1,20),10)
            q=F(rng.randint(-20,20),100)
            k=F(rng.randint(-20,20),100)
            r=flrw_ricci(H,q,k)
            self.assertEqual(-r['R00']+3*r['Rs'],r['R'])
            self.assertEqual(-r['TF00']+3*r['TFs'],0)
            self.assertEqual(r['tracefree_Ricci_sq'],3*(q-k)**2)

    def test_tt_sector_matches_scalar_induced_metric(self):
        m=ScalarModel(.01,.06,.4,2.9)
        s=(1,-.01,.2,-.1)
        r=responses(F(1,100),1,F(-1,100),F(1,5),F(-1,10),F(3,50),F(2,5))
        for expected, measured in zip(m.spectral(*s),r['theta']):
            self.assertAlmostEqual(expected,float(measured),places=13)

    def test_tensor_gap_exact(self):
        for q in (F(-1,10),F(-1,100),F(0),F(1,50)):
            r=responses(F(1,100),1,q)
            self.assertEqual(r['gap'],F(1,50)*q*r['WE']*r['WB'])

    def test_discriminant_identity_exhaustive(self):
        for ws in (F(1),F(2,3),F(7,4)):
            for we in (F(1),F(3,2),F(10,9)):
                for wb in (F(1),F(13,11),F(4,3)):
                    s=tt_symbol(ws,we,wb)
                    self.assertEqual(s['discriminant'],-4*ws**2*(we-wb)**2)
                    self.assertEqual(s['real_characteristic'],we==wb)
                    for x in (F(-2),F(0),F(1),F(3)):
                        self.assertEqual(tt_symbol_at(s,x),
                            ws**2/F(2)*(x-1)**2+2*(we*x-wb)**2)

    def test_strict_gate_passes_exact_de_sitter(self):
        r=tt_gate(F(1,100),1,0)
        self.assertTrue(r['strict_principal_gate_pass'])
        self.assertEqual(r['symbol']['discriminant'],0)
        self.assertEqual(tt_symbol_at(r['symbol'],1),0)

    def test_nonflat_gate_when_hdot_matches_curvature(self):
        r=tt_gate(F(1,100),1,F(1,50),curvature=F(1,50))
        self.assertTrue(r['strict_principal_gate_pass'])
        self.assertEqual(r['Ricci']['tracefree_Ricci_sq'],0)

    def test_nonflat_gate_rejects_non_einstein(self):
        r=tt_gate(F(1,100),1,0,curvature=F(1,50))
        self.assertFalse(r['strict_principal_gate_pass'])
        self.assertLess(r['symbol']['discriminant'],0)

    def test_negative_discriminant_iff_nonzero_curvature(self):
        for h in (F(1,2),F(1),F(2)):
            for q in (F(-3,100),F(-1,100),F(0),F(1,100),F(3,100)):
                r=tt_gate(F(1,1000),h,q)
                self.assertEqual(r['strict_principal_gate_pass'],q==0)
                self.assertEqual(r['symbol']['discriminant']<0,q!=0)
                self.assertLessEqual(r['symbol']['discriminant'],0)

    def test_frequency_imaginary_positive_for_nonzero_gap(self):
        for q in (F(-1,20),F(-1,100),F(1,50)):
            r=tt_gate(F(1,100),1,q)
            self.assertGreater(r['frequency']['imag_abs'],0)
        self.assertEqual(tt_gate(F(1,100),1,0)['frequency']['imag_abs'],0)

    def test_scale_of_discriminant(self):
        for q in (F(-1,1000),F(-1,100),F(-1,20)):
            g=tt_gate(F(1,100),1,q)
            v=g['responses'];p=g['Ricci'];d=g['symbol']['discriminant']
            self.assertEqual(d,-F(16,3)*v['beta']**2*v['Ws']**2*
                             v['WE']**2*v['WB']**2*p['tracefree_Ricci_sq'])

    def test_positive_domain_rejection(self):
        with self.assertRaises(ValueError):responses(F(1),1,1)
        with self.assertRaises(ValueError):responses(F(-1,100),1,0)
        with self.assertRaises(ValueError):responses(F(1,100),1,0,phidot=10,alpha=1)

class CovariantGateTests(unittest.TestCase):
    def setUp(self):
        self.m=ScalarModel(.01,.06,.4,2.978590919530843)

    def test_vacuum_de_sitter_trace_normalization(self):
        for beta in (.001,.01,.02):
            lam=de_sitter_lambda(1,beta)
            model=ScalarModel(beta,6*beta,.4,lam)
            r=gfield_curvature_trace(model,1,0,0,0)
            self.assertAlmostEqual(r['required_D_minus_3kappaT'],0,places=10)

    def test_source_geometric_trace_first_order(self):
        model=ScalarModel(1e-8,6e-8,.4,2.98)
        r=gfield_curvature_trace(model,1,-.01,.2,-.1)
        self.assertAlmostEqual(r['R_G'],18*(1.99),places=5)

    def test_explicit_missing_covariant_components_fail_closed(self):
        with self.assertRaises(TypeError):covariant_equation_residuals(1,3,1,{})

    def test_full_component_residuals_when_independently_supplied(self):
        # Synthetic values engineered for exact satisfaction; validator only.
        c=CovariantComponents(X00=5,Xs=13,rho=1,pressure=2,
            R_G=9,D=-21,Lambda_G=2,dX00=1,dRG=4,dD=0,
            dLambdaG=.5,drho=.25)
        r=covariant_equation_residuals(1,3,2,c)
        self.assertEqual(r['trace_free'],0)
        self.assertEqual(r['weyl_trace'],0)
        self.assertEqual(r['joint_noether'],0)
        self.assertTrue(r['all_checked'])
        self.assertNotEqual(covariant_equation_residuals(1,3,2,
                            replace(c,D=c.D+1))['weyl_trace'],0)
        self.assertNotEqual(covariant_equation_residuals(1,3,2,
                            replace(c,drho=c.drho+1))['joint_noether'],0)
        self.assertNotEqual(covariant_equation_residuals(1,3,2,
                            replace(c,Xs=c.Xs+1))['trace_free'],0)

    def test_tracefree_vacuum_shift_invariant(self):
        c=CovariantComponents(5,13,1,2,9,-21,2,1,4,0,.5,.25)
        cv=replace(c,rho=c.rho+7,pressure=c.pressure-7)
        r=covariant_equation_residuals(1,3,2,c)
        v=covariant_equation_residuals(1,3,2,cv)
        self.assertEqual(r['trace_free'],v['trace_free'])

    def test_reduced_spatial_el_independent_derivative(self):
        for z in reference_experiment()['curve']:
            s=tuple(z[k] for k in ('H','Hdot','phi','phidot'))
            a=spatial_minisuperspace_residual(self.m,s,step=1e-4)['spatial_EL']
            b=spatial_minisuperspace_residual(self.m,s,step=5e-5)['spatial_EL']
            self.assertLess(abs(a),2e-8)
            self.assertLess(abs(b),2e-8)
            self.assertLess(abs(a-b),2e-9)

    def test_invalid_step(self):
        with self.assertRaises(ValueError):
            spatial_minisuperspace_residual(self.m,(1,-.01,.2,-.1),0)

    def test_source_component_requires_derivatives(self):
        # Explicit constructor fields prevent a source-free purported tensor audit.
        with self.assertRaises(TypeError):
            CovariantComponents(5,13,1,2,9,-21,2)

    def test_reference_audit_fails_tt_gate_at_all_samples(self):
        r=reference_audit()
        self.assertFalse(r['full_covariant_tensor_evidence'])
        self.assertEqual(len(r['entries']),6)
        self.assertTrue(all(not x['tt_gate_pass'] for x in r['entries']))
        self.assertTrue(all(x['Ricci_TF2']>0 for x in r['entries']))
        self.assertTrue(all(x['tt_discriminant']<0 for x in r['entries']))
        self.assertTrue(all(abs(x['spatial_reduced_EL'])<2e-8 for x in r['entries']))

    def test_lambda_target_evolves_nontrivially(self):
        r=reference_audit()['entries']
        target=[x['required_D_minus_3kappaT'] for x in r]
        self.assertGreater(abs(target[0]-target[-1]),.2)
        self.assertTrue(all(math.isfinite(x) for x in target))

if __name__=='__main__': unittest.main()
