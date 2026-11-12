"""TOE-15: tensor SO(2), Gaussian determinant, and source multiplet cone tests."""
import unittest
from fractions import Fraction as F
from random import Random
from research.toe.helicity_constraint import (
    spin_two_generator, equivariance_certificate, helicity_hermitian,
    det3_gaussian, trial_tensor_six, trial_helicity_certificate,
    trial_helicity_polynomial, outer, combine_outer, two_multiplet_witness,
    source_response_match, reference_experiment, _rank, _matmul,
    d_one_at_point, local_dirac_kahler_jet_witness
)
from research.toe.tensor_subspace import default_params
from research.toe.cone_matching import cone_certificate


class TensorHelicityTests(unittest.TestCase):
    def test_generator_square_and_antisymmetry(self):
        j=spin_two_generator()
        jj=_matmul(j,j)
        self.assertEqual(jj,tuple(tuple(F(-1) if i==k else F() for k in range(6)) for i in range(6)))
        self.assertTrue(all(j[i][k]==-j[k][i] for i in range(6) for k in range(6)))

    def test_entire_toe13_six_mode_is_equivariant(self):
        for omega in (F(-3,2),F(-1),F(-1,3),F(0),F(2,5),F(1),F(7,3)):
            p=trial_tensor_six(omega)
            self.assertTrue(equivariance_certificate(p))
            self.assertEqual(helicity_hermitian(p)[0][0][1],0)

    def test_helicity_determinant_square_exact(self):
        for omega in (F(-2),F(-7,4),F(-1,3),F(0),F(2,5),F(1),F(3,2),F(5,2)):
            r=trial_helicity_certificate(omega)
            self.assertEqual(r['six_mode_determinant'],r['helicity_determinant']**2)
            self.assertTrue(r['SO2_equivariant'])

    def test_helicity_polynomial_reconstruction(self):
        coeff=trial_helicity_polynomial()
        self.assertEqual(len(coeff),9)
        for omega in (F(0),F(-7,5),F(11,7),F(5)):
            observed=trial_helicity_certificate(omega)['helicity_determinant']
            expected=sum((v*omega**i for i,v in enumerate(coeff)),F())
            self.assertEqual(observed,expected)

    def test_zero_vector_curvature_preserves_group(self):
        for omega in (F(0),F(1),F(3,2)):
            r=trial_helicity_certificate(omega,sigma1=0)
            self.assertTrue(r['six_mode_det_square'])

    def test_random_real_symmetric_spin2_blocks_are_squares(self):
        rng=Random(1501)
        for k in range(30):
            h=[[F() for _ in range(6)] for _ in range(6)]
            for f in range(3):
                for g in range(f,3):
                    a=F(rng.randint(-3,3),rng.randint(1,5))
                    b=F() if f==g else F(rng.randint(-3,3),rng.randint(1,5))
                    x,y=2*f,2*g
                    h[x][y]=h[x+1][y+1]=a
                    h[x][y+1]=b;h[x+1][y]=-b
                    if f!=g:
                        h[y][x]=a;h[y+1][x+1]=a
                        h[y+1][x]=b;h[y][x+1]=-b
            m=tuple(tuple(row) for row in h)
            c=helicity_hermitian(m)
            d=det3_gaussian(c)
            from research.toe.mixed_principal import det
            self.assertEqual(d[1],0)
            self.assertEqual(det(m),d[0]**2)

    def test_non_equivariant_matrix_rejected(self):
        m=[list(row) for row in trial_tensor_six(0)]
        m[0][0]+=1
        with self.assertRaises(AssertionError):equivariance_certificate(m)
        with self.assertRaises(ValueError):equivariance_certificate(((1,2),(3,4)))


class MultipletRankAndResponseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.w=two_multiplet_witness()

    def test_exact_isotropic_rank_three_from_two_rank_two_multiplets(self):
        self.assertEqual(self.w['individual_ranks'],(2,2))
        self.assertEqual(self.w['rank'],3)
        self.assertEqual(self.w['number_of_multiplets'],2)
        m=self.w['combined']
        self.assertEqual(tuple(m[i][i] for i in range(6)),(0,0,0,2,2,2))
        self.assertEqual(_rank(m),3)
        for i in range(6):
            for j in range(6):
                if i!=j:self.assertEqual(m[i][j],0)

    def test_one_rank_two_block_cannot_generate_rank_three_magnetic(self):
        self.assertLess(_rank(self.w['m1']),3)
        self.assertLess(_rank(self.w['m2']),3)

    def test_source_eq40_exact_reference_response_repair(self):
        q=source_response_match(mE=self.w['mE'],mB=self.w['mB'])
        self.assertEqual(q['thetaE'],F(124,125))
        self.assertEqual(q['thetaB'],F(124,125))
        self.assertEqual(q['thetaS'],F(122,125))
        self.assertEqual(q['compensation_residual'],0)
        self.assertEqual(q['discriminant'],0)
        self.assertTrue(q['cone_matched'])

    def test_detuning_in_either_direction_opens_negative_discriminant(self):
        for eps in (F(-1,2),F(-1,1000),F(1,10000),F(1,10)):
            q=source_response_match(mB=2+eps)
            self.assertFalse(q['cone_matched'])
            self.assertLess(q['discriminant'],0)
            we,wb,ws=q['WE'],q['WB'],q['Ws']
            self.assertEqual(q['discriminant'],-4*ws*ws*(we-wb)**2)
            self.assertEqual(we-wb, (F(3,500)*eps)/(q['thetaE']*q['thetaB']))

    def test_multiplet_cone_does_not_infer_background_field_equations(self):
        r=reference_experiment()
        self.assertTrue(r['source_reference_cone_matched'])
        self.assertEqual(r['source_two_multiplet_algebraic_rank'],3)
        self.assertTrue(r['source_multiplet_pointwise_D_jets_realized'])
        self.assertFalse(r['source_multiplet_jet_integrability_verified'])
        self.assertFalse(r['source_multiplet_background_equations_solved'])
        self.assertFalse(r['complete_constrained_GfE_YM_tensor_system_derived'])
        self.assertFalse(r['strong_hyperbolicity_verified'])

    def test_source_response_guard_for_positive_spectrum(self):
        with self.assertRaises(ValueError):source_response_match(alpha=0)
        with self.assertRaises(ValueError):source_response_match(beta=0)
        with self.assertRaises(ValueError):source_response_match(mB=-1000)

    def test_explicit_truncated_dirac_kahler_first_jets(self):
        jets=local_dirac_kahler_jet_witness()
        self.assertTrue(jets['local_jet_realized'])
        self.assertFalse(jets['global_isotropy_verified'])
        self.assertFalse(jets['eom_satisfied'])
        self.assertEqual(jets['two_form_differential'],(0,0,0,0,0,1))
        self.assertEqual(jets['Dphi_0'],(0,0))
        self.assertEqual(jets['Dphi_1'],((0,)*4,(0,)*4))
        self.assertEqual(jets['total_bivector_response'],self.w['combined'])
        self.assertEqual(jets['one_form_gradient'][1][2],F(1,2))
        self.assertEqual(jets['one_form_gradient'][2][1],-F(1,2))

    def test_exterior_first_jet_is_antisymmetric(self):
        rng=Random(1502)
        for _ in range(100):
            g=[[F(rng.randrange(-7,8),3) for j in range(4)] for i in range(4)]
            dg=d_one_at_point(g)
            dgt=d_one_at_point(tuple(tuple(g[j][i] for j in range(4)) for i in range(4)))
            self.assertEqual(dg,tuple(-v for v in dgt))
            for mu in range(4):g[mu][mu]+=rng.randrange(-5,6)
            self.assertEqual(dg,d_one_at_point(g))
        with self.assertRaises(ValueError):d_one_at_point(((0,0),)*2)

    def test_rank_checker_rejects_bad_dimensions(self):
        with self.assertRaises(ValueError):_rank(())
        with self.assertRaises(ValueError):_rank(((1,2),(3,)))
        with self.assertRaises(ValueError):combine_outer((1,2),(3,4),2)


if __name__=='__main__':unittest.main()
