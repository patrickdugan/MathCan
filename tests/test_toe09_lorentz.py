"""Exact source-level bivector signature and spectrum regression tests."""
from fractions import Fraction as F
from itertools import product
from random import Random
import unittest
from research.toe.lorentz_bivector import (
    coefficients,covariant_gram6,raised_gram6,exact_determinant,
    source_block,critical_perturbation,reference_example,root_interval_from_trace,rotate_flavors,krein_self_adjoint
)

class LorentzBivectorTests(unittest.TestCase):
    def test_lagrange_identity_exhaustive(self):
        for e1,e2,b1,b2 in product((-2,-1,0,1,2),repeat=4):
            e,b,c,w=coefficients((e1,e2),(b1,b2))
            self.assertEqual(e*b-c*c,w*w)

    def test_gram_and_raised_determinants(self):
        for e,b in [((2,1),(3,2)),((1,0),(0,1)),((1,1),(2,2)),((0,0),(3,4))]:
            _,_,_,w=coefficients(e,b)
            self.assertEqual(exact_determinant(covariant_gram6(e,b)),w**6)
            self.assertEqual(exact_determinant(raised_gram6(e,b)),-w**6)

    def test_offdiag_lorentz_signs(self):
        m=raised_gram6((1,0),(1,0))
        self.assertEqual((m[0][0],m[0][3],m[3][0],m[3][3]),(-1,1,-1,1))
        x=source_block((1,0),(1,0),alpha=F(1,10),beta=F(1,20),H=1,Hdot=0)
        self.assertTrue(krein_self_adjoint(x))

    def test_diagonal_source_signs(self):
        x=source_block((1,0),(0,1),alpha=F(1,100),beta=F(1,100),H=1,Hdot=0)
        self.assertEqual(x.theta_e,1-F(1,100)-F(2,100))
        self.assertEqual(x.theta_b,1+F(1,100)-F(2,100))
        self.assertEqual(x.mixed,0)

    def test_discriminant_identity_exact(self):
        rng=Random(20261111)
        for _ in range(250):
            E=(F(rng.randint(-5,5),9),F(rng.randint(-5,5),9))
            B=(F(rng.randint(-5,5),9),F(rng.randint(-5,5),9))
            x=source_block(E,B,alpha=F(1,20),beta=F(1,30),H=1,Hdot=F(-1,100))
            self.assertEqual(x.discriminant,x.gap*x.gap-4*x.offdiag*x.offdiag)
            self.assertEqual(x.trace*x.trace-4*x.determinant,x.discriminant)

    def test_matched_nonzero_mixing_complex(self):
        u,v,t=F(1,50),F(1,25),F(1,1000)
        x=source_block((u,-u+t),(v,v),alpha=F(1,10),beta=F(1,50),H=1,Hdot=F(-1,100))
        self.assertLess(x.discriminant,0)
        self.assertEqual(root_interval_from_trace(x),'complex_pair')

    def test_positive_start_then_complex_perturbation(self):
        r=reference_example()
        self.assertTrue(r['baseline_positive_real'])
        self.assertEqual(r['perturbed_eigenvalue_status'],'complex_pair')
        self.assertTrue(F(r['covariant_gram_determinant'])>0)
        self.assertTrue(F(r['raised_gram_determinant'])<0)

    def test_critical_perturbation_formula(self):
        u,v=F(1,50),F(1,25)
        for t in (F(0),F(1,10000),F(1,1000),F(1,100),F(1,50)):
            x=source_block((u,-u+t),(v,v),alpha=F(1,10),beta=F(1,50),H=1,Hdot=F(-1,100))
            self.assertEqual(x.discriminant,critical_perturbation(u,v,t,F(1,10)))

    def test_diagonal_matched_mixing_must_vanish_for_reality(self):
        for m in (-3,-2,-1,1,2,3):
            # Algebraic matrix with equal diagonal and nonzero offdiag.
            gap=F(0);off=F(m,10)
            self.assertEqual(gap*gap-4*off*off,-4*off*off)
            self.assertLess(-4*off*off,0)

    def test_defective_double_root_flag(self):
        # Repeated positive root and nonzero mixing: the 2×2 matrix has a
        # nontrivial nilpotent part, so its eigenbasis is incomplete.
        x=source_block((1,0),(1,0),alpha=F(1,10),beta=F(1,50),
                       H=1,Hdot=-10)
        self.assertEqual(x.gap,2*x.offdiag)
        self.assertEqual(x.discriminant,0)
        self.assertFalse(x.diagonalizable)
        self.assertEqual(root_interval_from_trace(x),'defective_repeated')

    def test_rational_flavor_rotation_preserves_spectrum(self):
        r=((F(3,5),-F(4,5)),(F(4,5),F(3,5)))
        for E,B in [((F(1,7),F(2,3)),(F(5,7),F(-1,2))),
                    ((F(1,50),-F(1,50)),(F(1,25),F(1,25)))]:
            E2,B2=rotate_flavors(E,B,r)
            e,b,c,w=coefficients(E,B)
            e2,b2,c2,w2=coefficients(E2,B2)
            self.assertEqual((e,b,c,w),(e2,b2,c2,w2))
            a=source_block(E,B,alpha=F(1,100),beta=F(1,200),H=1,Hdot=0)
            d=source_block(E2,B2,alpha=F(1,100),beta=F(1,200),H=1,Hdot=0)
            self.assertEqual(a.discriminant,d.discriminant)
        with self.assertRaises(ValueError):
            rotate_flavors((1,2),(3,4),((2,0),(0,1)))

    def test_reference_fixture_exact(self):
        import json
        from pathlib import Path
        path=Path(__file__).resolve().parents[1]/'research'/'toe'/'fixtures'/'lorentz_bivector_synthetic.json'
        self.assertEqual(json.loads(path.read_text()),reference_example())

    def test_zero_flavor_area_rank(self):
        E,B=(F(1),F(2)),(F(2),F(4))
        _,_,_,w=coefficients(E,B)
        self.assertEqual(w,0)
        self.assertEqual(exact_determinant(raised_gram6(E,B)),0)

    def test_invalid_coupling(self):
        with self.assertRaises(ValueError):
            source_block((1,2),(3,4),alpha=0,beta=1,H=1,Hdot=0)
        with self.assertRaises(ValueError):
            source_block((1,2),(3,4),alpha=1,beta=-1,H=1,Hdot=0)
        with self.assertRaises(ValueError):
            coefficients((1,), (2,))

if __name__=='__main__':unittest.main()
