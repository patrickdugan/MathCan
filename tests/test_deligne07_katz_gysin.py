"""DEL-07 rational Poincare-dual Frobenius checks."""
import random
import unittest
from fractions import Fraction as F

from research.deligne_sign_audit.del07_oracle import (
    add, transpose, rank, mat, eye, power,
    example, gysin, compact_frob, compose_certificate,
    kernel_action_certificate, wrong_forward_dual_certificate,
)
from research.deligne_sign_audit.del07_verify_tasks import verify
from research.deligne_sign_audit.geometry_trace import multiply, trace


class KatzPoincareGysinTests(unittest.TestCase):
    def test_entire_64_case_mutation_corpus(self):
        self.assertEqual(sum(verify().values()),64)

    def test_transpose_and_rank_exact(self):
        M=mat([[1,2],[3,4],[5,6]])
        self.assertEqual(transpose(M),mat([[1,3,5],[2,4,6]]))
        self.assertEqual(rank(M),2)
        self.assertEqual(rank(mat([[1,0],[0,0],[0,0]])),1)

    def test_perfect_pairing_transpose_gysin_surjectivity(self):
        for a in (1,2,3,7):
            R,PX,PY,AX,AY=example(a=a,b=5,c=11)
            G=gysin(R,PX,PY)
            self.assertEqual(rank(R),2)
            self.assertEqual(rank(G),2)
            self.assertEqual(len(G),2)
            self.assertEqual(len(G[0]),3)

    def test_boundary_kernel_equivariance_and_all_powers(self):
        rng=random.Random(261100797)
        for _ in range(50):
            a,b,c=(rng.randint(1,9) for j in range(3))
            u,v,p,s,t=(rng.randint(-9,9) for j in range(5))
            R,PX,PY,AX,AY=example(
                a=a,b=b,c=c,u=u,v=v,p=p,s=s,t=t)
            for n in (1,2,3,4,7):
                r=kernel_action_certificate(R,PX,PY,AX,AY,n=n)
                self.assertTrue(r["restriction_injective"])
                self.assertTrue(r["gysin_surjective"])
                self.assertTrue(r["restriction_equivariant"])
                self.assertTrue(r["gysin_equivariant"])
                self.assertTrue(r["gysin_annihilates_generator"])
                self.assertTrue(r["frob_preserves_kernel"])
                self.assertTrue(r["generator_is_eigenvector"])
                self.assertTrue(r["trace_difference_matches"])
                self.assertEqual(r["trace_difference"],F(c)**n)

    def test_frobenius_inverse_action_and_dual(self):
        R,PX,PY,AX,AY=example()
        good=compose_certificate(R,PX,PY,AX,AY)
        self.assertTrue(good["gysin_equivariant"])
        self.assertFalse(wrong_forward_dual_certificate(R,PX,PY,AX,AY))

    def test_injective_restriction_is_essential(self):
        R,PX,PY,AX,AY=example()
        badR=mat([[1,0],[0,0],[0,0]])
        AX=mat([[2,0],[0,3]])
        AY=mat([[2,0,0],[0,3,0],[0,0,5]])
        r=compose_certificate(badR,PX,PY,AX,AY)
        self.assertFalse(r["restriction_injective"])
        self.assertFalse(r["gysin_surjective"])
        self.assertTrue(r["restriction_equivariant"])
        self.assertTrue(r["gysin_equivariant"])

    def test_wrong_frobenius_square_is_detected(self):
        R,PX,PY,AX,AY=example()
        badAY=mat([[2,1,7],[0,3,-2],[1,0,5]])
        r=compose_certificate(R,PX,PY,AX,badAY)
        self.assertFalse(r["restriction_equivariant"])
        self.assertFalse(r["gysin_equivariant"])

    def test_nonperfect_duality_rejected(self):
        R,PX,PY,AX,AY=example()
        with self.assertRaisesRegex(ValueError,"singular"):
            gysin(R,mat([[1,0],[0,0]]),PY)

    def test_perverse_shift_and_compact_degree_exact(self):
        for D in range(1,13):
            boundary_a=D-1
            boundary_j=2*D-2-boundary_a
            self.assertEqual(boundary_j,D-1)
            self.assertEqual(boundary_j+2,D+1)
            for a in range(-3,D-1):
                j=2*D-2-a
                self.assertGreater(j,D-1)
                self.assertEqual(j+2,2*D-a)

    def test_tate_twist_inverse_action_requires_power_n(self):
        r=5
        eigen=F(2,3)
        for n in range(1,8):
            self.assertEqual((r*eigen)**n,r**n*eigen**n)
        self.assertNotEqual((r*eigen)**3,r*eigen**3)


if __name__=="__main__":
    unittest.main()
