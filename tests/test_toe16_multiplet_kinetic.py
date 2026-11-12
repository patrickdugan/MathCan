"""TOE-16 exact rational dynamic-source / two-form Hessian tests."""
import unittest
from fractions import Fraction as F
from random import Random
from research.toe.multiplet_kinetic import (
    identity3, dot, outer3, gram3, is_scalar_identity3, witness_two,
    witness_three, check_witness, theta_magnetic, theta_matrix_at,
    source_kinetic_hessian, determinant_hessian_oracle,
    flavor_trace_matrix, flavor_trace_independent, rank_gate,
    static_magnetic_mixing, rotate_flavor_locked,reference_experiment,
    v3,matmul,transpose
)

class SourceKineticTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.two=witness_two()
        cls.three=witness_three()

    def test_matched_background_is_rank_three_in_both_cases(self):
        for w in (self.two,self.three):
            b=check_witness(w)
            self.assertEqual(b['mB'],2)
            self.assertEqual(b['rankM'],3)
            self.assertEqual(b['M'],tuple(tuple(F(2) if i==j else F()
                                  for j in range(3)) for i in range(3)))
            self.assertEqual(theta_magnetic(w),F(124,125))

    def test_two_has_rank_one_U_triplet_has_isotropic_U(self):
        b2=check_witness(self.two)
        b3=check_witness(self.three)
        self.assertEqual(b2['U'],((0,0,0),(0,0,0),(0,0,2)))
        self.assertEqual(b2['rankU'],1)
        self.assertFalse(is_scalar_identity3(b2['U']))
        self.assertEqual(b3['U'],identity3())
        self.assertEqual(b3['V'],identity3())
        self.assertTrue(is_scalar_identity3(b3['U']))
        self.assertEqual(b3['rankU'],3)

    def test_parallel_perpendicular_exact_gap(self):
        w=self.two
        transverse=((0,1,0),(0,0,0))
        longitudinal=((0,0,1),(0,0,0))
        perp=source_kinetic_hessian(w,transverse)
        para=source_kinetic_hessian(w,longitudinal)
        self.assertEqual(perp,F(-1479,123008))
        self.assertEqual(para,F(-735,61504))
        self.assertEqual(para-perp,F(9,123008))
        self.assertGreater(para-perp,0)

    def test_source_trace_exact_det_second_derivative(self):
        rng=Random(1601)
        for n,w in ((2,self.two),(3,self.three)):
            for _ in range(24):
                dirs=tuple(tuple(F(rng.randrange(-5,6),rng.randrange(1,6))
                                 for _ in range(3)) for _ in range(n))
                self.assertEqual(
                    source_kinetic_hessian(w,dirs),
                    determinant_hessian_oracle(w,dirs))

    def test_static_transverse_curl_first_variation_is_gauge_invariant(self):
        from research.toe.operator_principal import wave_field_strength
        k=(0,0,0,1)
        a=(0,1,2,3)
        long=tuple(a[i]+F(7,3)*k[i] for i in range(4))
        self.assertEqual(wave_field_strength(k,a),wave_field_strength(k,long))

    def test_flavor_trace_independent_polarization(self):
        rng=Random(1602)
        for w in (self.two,self.three):
            for alpha in (F(3,500),F(1,20)):
                for beta in (F(1,100),F(3,100)):
                    self.assertEqual(flavor_trace_matrix(w,alpha=alpha,beta=beta),
                        flavor_trace_independent(w,alpha=alpha,beta=beta))

    def test_two_flavor_trace_anisotropic(self):
        t=flavor_trace_matrix(self.two)
        self.assertEqual(t[0][0],t[1][1])
        self.assertEqual(t[2][2]-t[0][0],F(9,61504))
        self.assertFalse(is_scalar_identity3(t))
        self.assertFalse(rank_gate(self.two)['curl_flavor_trace_isotropic'])

    def test_three_flavor_trace_isotropic(self):
        t=flavor_trace_matrix(self.three)
        self.assertTrue(is_scalar_identity3(t))
        self.assertEqual(t[0][0],t[1][1])
        self.assertEqual(t[1][1],t[2][2])
        self.assertTrue(rank_gate(self.three)['curl_flavor_trace_isotropic'])

    def test_locked_triplet_rational_rotation_invariant(self):
        R=((F(3,5),F(-4,5),F()),(F(4,5),F(3,5),F()),(F(),F(),F(1)))
        A=((1,2,3),(-1,0,2),(F(3,5),1,-2))
        B=rotate_flavor_locked(A,R)
        self.assertEqual(source_kinetic_hessian(self.three,A),
                         source_kinetic_hessian(self.three,B))
        R2=((0,1,0),(0,0,1),(1,0,0))
        self.assertEqual(source_kinetic_hessian(self.three,A),
                         source_kinetic_hessian(self.three,rotate_flavor_locked(A,R2)))

    def test_invalid_rotations_rejected(self):
        with self.assertRaises(ValueError):
            rotate_flavor_locked(((0,0,0),)*3,((1,0,0),(0,1,0),(1,0,1)))
        with self.assertRaises(ValueError):
            check_witness({'u':[(0,0,1)],'v':[(0,0,1)],'lam':1})
        with self.assertRaises(ValueError):
            check_witness({'u':[(0,0,1)]*2,'v':[(1,0,0),(0,1,0)],'lam':0})

    def test_static_curvature_one_form_mixed_orientation(self):
        w=self.two
        h_z=[[0]*4 for _ in range(4)]
        h_z[1][1]=1;h_z[2][2]=-1
        h_y=[[0]*4 for _ in range(4)]
        h_y[1][1]=1;h_y[3][3]=-1
        a=(0,1,0,0)
        zz=static_magnetic_mixing(w,(0,0,0,1),h_z,a)
        yy=static_magnetic_mixing(w,(0,0,1,0),h_y,a)
        self.assertEqual(zz['curl_magnetic'],(0,1,0))
        self.assertEqual(yy['curl_magnetic'],(0,0,-1))
        self.assertEqual(zz['mixed_H'],0)
        self.assertEqual(yy['mixed_H'],F(-15,123008))
        self.assertNotEqual(zz['mixed_H'],yy['mixed_H'])

    def test_mixed_curl_pure_gauge_amplitude_zero(self):
        h=[[0]*4 for _ in range(4)]
        h[1][1]=1;h[3][3]=-1
        k=(0,0,1,0)
        base=static_magnetic_mixing(self.two,k,h,(0,1,0,0))['mixed_H']
        shifted=static_magnetic_mixing(self.two,k,h,(0,1,4,0))['mixed_H']
        self.assertEqual(base,shifted)

    def test_rank_two_upper_bound_general_random(self):
        rng=Random(1612)
        for _ in range(120):
            u=tuple(tuple(rng.randrange(-3,4) for _ in range(3)) for _ in range(2))
            U=gram3(u)
            self.assertLessEqual(_rank3(U),2)
            if is_scalar_identity3(U):
                self.assertEqual(U,((0,0,0),(0,0,0),(0,0,0)))
                self.assertEqual(u,((0,0,0),(0,0,0)))

    def test_receipt_keeps_all_physics_gates_false(self):
        r=reference_experiment()
        self.assertEqual(r['two_multiplet_parallel_perpendicular_gap'],'9/123008')
        self.assertFalse(r['two_multiplet_curl_trace_isotropic'])
        self.assertTrue(r['three_multiplet_curl_trace_isotropic'])
        self.assertFalse(r['full_principal_isotropy_verified'])
        self.assertFalse(r['source_background_equations_solved'])
        self.assertFalse(r['physical_constraints_eliminated'])
        self.assertFalse(r['strong_hyperbolicity_verified'])


def _rank3(a):
    from research.toe.helicity_constraint import _rank
    return _rank(a)


if __name__=='__main__':
    unittest.main()
