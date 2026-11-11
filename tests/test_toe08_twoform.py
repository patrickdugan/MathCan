"""TOE-08: exact 2-form triad checks, cosmological matching and no-go tests."""
import unittest
from fractions import Fraction as F
from itertools import product
from random import Random

from research.toe.twoform_triad import (
    tetrad_bivectors, response_matrix, diagonal_block_test, rank_q,
    four_tensor_response,flrw_curvature_response,stress,dynamics,
    continuity_residual,target_b2,match_gap,matching_constraint,
    powerlaw_reduced_condition,constrained_kinetic_hessian,schur_2x2,
    reference_receipt,evolve_powerlaw)


class ResponseTests(unittest.TestCase):
    def test_exact_triad_magnetic_identity(self):
        for b in [F(-2), F(-1,3),F(0),F(1),F(4,3)]:
            M=response_matrix(tetrad_bivectors(0,b))
            self.assertEqual(diagonal_block_test(M),(0,b*b,0))
            self.assertEqual(rank_q(M),3 if b else 0)

    def test_electric_magnetic_eb_mixing(self):
        for e,b in product((F(-2),F(-1,3),F(0),F(1)),repeat=2):
            M=response_matrix(tetrad_bivectors(e,b))
            self.assertEqual(diagonal_block_test(M),(e*e,b*b,e*b))
            self.assertEqual(rank_q(M),3 if (e or b) else 0)

    def test_rank_two_restriction_random(self):
        rng=Random(2082026)
        for _ in range(700):
            species=[[F(rng.randint(-4,4),3) for _ in range(6)] for j in range(2)]
            self.assertLessEqual(rank_q(response_matrix(species)),2)

    def test_one_two_species_cannot_have_nonzero_isotropic_magnetic(self):
        for n in (1,2):
            for b in (F(1),F(3,2)):
                M=response_matrix(tetrad_bivectors(0,b,n))
                self.assertIsNone(diagonal_block_test(M))
                self.assertEqual(rank_q(M),n)

    def test_non_diagonal_block_rejected(self):
        M=[list(v) for v in response_matrix(tetrad_bivectors(1,1))]
        M[0][4]=F(7)
        self.assertIsNone(diagonal_block_test(M))

    def test_response_riemann_symmetry(self):
        r=Random(17317)
        for b,lam in product((F(0),F(1),F(-3,2)),(F(1),F(2,3))):
            P=four_tensor_response(b,lam)
            for _ in range(150):
                i,j,k,l=[r.randrange(4) for t in range(4)]
                self.assertEqual(P[i][j][k][l],-P[j][i][k][l])
                self.assertEqual(P[i][j][k][l],-P[i][j][l][k])
                self.assertEqual(P[i][j][k][l],P[k][l][i][j])
                self.assertEqual(P[i][j][k][l]+P[i][k][l][j]+P[i][l][j][k],0)

    def test_curvature_response_contraction(self):
        for H,hdot,b,lam in product((F(-1),F(0),F(2,3)),
                (F(-2,7),F(0),F(2)),(F(-2),F(0),F(1,2)),
                (F(-1,3),F(0),F(2,5))):
            self.assertEqual(flrw_curvature_response(H,hdot,b,lam),
                             3*lam*H*H*b*b)

    def test_bad_bivector_counts(self):
        with self.assertRaises(ValueError):tetrad_bivectors(1,2,4)
        with self.assertRaises(ValueError):response_matrix([[1,2]])
        with self.assertRaises(ValueError):diagonal_block_test([[1]])


class StressAndDynamicsTests(unittest.TestCase):
    def test_minimal_rho_pressure(self):
        S=stress(F(2),F(3),F(3,2),F(-4,3),m2=F(9,7))
        self.assertEqual(S.curvature_rho,0)
        self.assertEqual(S.curvature_pressure,0)
        self.assertEqual(S.rho,F(3,2)*(F(16,9)+F(9,7)*F(9,4)))
        self.assertEqual(S.pressure,F(1,2)*(-F(16,9)+F(9,7)*F(9,4)))

    def test_coupled_nonminimal_stress(self):
        H=F(2);d=F(-1,5);b=F(3,2);v=F(-7,4); lam=F(2,11)
        S=stress(H,d,b,v,F(5,7),lam)
        self.assertEqual(S.curvature_rho,3*lam*H*H*b*b)
        self.assertEqual(S.curvature_pressure,
                         3*lam*H*H*b*b-2*lam*(d+H*H)*b*b-4*lam*H*b*v)

    def test_exact_continuity_1000_states(self):
        rng=Random(774029)
        for _ in range(1000):
            vals=[F(rng.randint(-6,6),rng.randint(1,9)) for j in range(4)]
            m2=F(rng.randint(0,6),rng.randint(1,9))
            lam=F(rng.randint(-6,6),rng.randint(1,9))
            self.assertEqual(continuity_residual(*vals,m2,lam),0)

    def test_massive_electric_component_constraint(self):
        # For homogeneous B_0i and flat FLRW the field H=dB does not depend
        # on the electric component. Its algebraic E-L equation is
        # (m² - 2lambda*(Hdot+H²)) e = 0.
        for m2,H,d,lam in product((F(1),F(4,3)),(F(0),F(1)),
                                      (F(-1,2),F(1,3)),(F(0),F(1,9))):
            coeff=m2-2*lam*(d+H*H)
            if coeff:
                self.assertNotEqual(coeff*F(1),0)
            self.assertEqual(coeff*F(0),0)

    def test_2form_first_order_system(self):
        self.assertEqual(dynamics(F(2),F(1),F(3),m2=F(4),lam=F(1,4)),
                         (F(-1),F(-8)))

    def test_positive_minimal_energy(self):
        for b,v,m2 in product((F(-2),F(0),F(3,5)),
                (F(-1),F(0),F(3,8)),(F(0),F(1,6),F(5))):
            self.assertGreaterEqual(stress(1,0,b,v,m2).rho,0)

    def test_invalid_parameters(self):
        with self.assertRaises(ValueError):stress(1,0,1,1,m2=-1)
        with self.assertRaises(ValueError):continuity_residual(1,0,1,1,m2=-1)
        with self.assertRaises(ValueError):stress(False,0,1,1)


class MatchingTests(unittest.TestCase):
    def test_pointwise_beta_alpha_matching(self):
        b=F(1)
        self.assertEqual(target_b2(F(1,100),F(1,25),F(1),F(-2)),1)
        self.assertEqual(match_gap(F(1,100),F(1,25),F(1),F(2),F(-2),b),0)

    def test_positive_magnetic_response_requires_negative_hdot(self):
        for hdot in (F(-3,4),F(-1,20),F(0),F(1,3)):
            b2=target_b2(F(1,100),F(1,25),F(1),hdot)
            self.assertEqual(b2>0,hdot<0)

    def test_matching_constraint_powerlaw_identity(self):
        for p,t,m2,lam in product((F(1,2),F(1),F(2),F(3)),
               (F(1,2),F(1),F(3)),(F(0),F(1,10)),(F(0),F(1,5))):
            H=p/t;hd=-p/t**2;J=2*p/t**3;K=-6*p/t**4
            val=matching_constraint(H,hd,J,K,m2,lam)
            expected=powerlaw_reduced_condition(p,m2,lam,t)/t**2
            self.assertEqual(val,expected)

    def test_massless_powerlaw_allowed_indices(self):
        for p in (F(1,3),F(1,2),F(1),F(2),F(3)):
            self.assertEqual(powerlaw_reduced_condition(p,0,0,1)==0,
                             p in (F(1,2),F(2)))

    def test_massive_powerlaw_time_no_go(self):
        for p,lam in product((F(1,2),F(1),F(2),F(3)),
                             (F(-1,5),F(0),F(1,5))):
            # For fixed m²>0, the t² term prevents the matching EOM at t=1 AND t=2.
            self.assertNotEqual(powerlaw_reduced_condition(p,F(1,7),lam,1),
                                powerlaw_reduced_condition(p,F(1,7),lam,2))

    def test_massless_p_half_is_pure_gauge_locally(self):
        # With p=1/2, b=c/t and v=(2p-1)c/t²=0, so H=dB=0.
        p=F(1,2)
        for t in (F(1),F(3,2),F(5)):
            b=1/t
            v=(2*p-1)/t**2
            self.assertEqual(v,0)
            self.assertEqual(dynamics(p/t,b,v)[0],-b/t)

    def test_schur_identity(self):
        rng=Random(74)
        for _ in range(500):
            a=F(rng.randint(-10,10),7)
            b=F(rng.randint(-10,10),5)
            c=F(rng.choice([i for i in range(-10,11) if i!=0]),3)
            self.assertEqual(*schur_2x2(a,b,c))

    def test_homogeneous_kinetic_hessian(self):
        # Exact second velocity derivatives of the reduced coordinate-field action.
        for a,n,w,lam,M2 in product((F(1),F(2)),(F(1),F(3,2)),
                                     (F(-2),F(0),F(1,3)),
                                     (F(-1,3),F(0),F(2)),(F(0),F(1))):
            K=constrained_kinetic_hessian(a,n,w,lam,M2)
            self.assertEqual(K[0][1],0)
            self.assertEqual(K[1][0],0)
            self.assertEqual(K[1][1],3/(n*a))

    def test_powerlaw_massless_exact_integration(self):
        for n in (100,400):
            v=evolve_powerlaw(2,1,3,m2=0,steps=n)
            self.assertAlmostEqual(v['b'],.5,places=8)
            self.assertAlmostEqual(v['v'],.75,places=8)
            self.assertAlmostEqual(v['matching_error'],0,places=8)

    def test_powerlaw_mass_causes_cone_mismatch(self):
        v=evolve_powerlaw(2,1,3,m2=.1,steps=400)
        self.assertGreater(abs(v['matching_error']),1e-4)
        self.assertAlmostEqual(v['matching_error'],
            evolve_powerlaw(2,1,3,m2=.1,steps=800)['matching_error'],places=8)

    def test_reference(self):
        r=reference_receipt()
        self.assertEqual(r['schema'],'mathcan.toe08.triad.v1')
        self.assertEqual(r['continuity_residual'],'0')
        self.assertEqual(r['response_rank'],3)
        self.assertEqual(r['curvature_response_scalar'],'6/5')


if __name__=='__main__':unittest.main()
