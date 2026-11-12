"""TOE-13: independent auxiliary G Schur complements for TT Ricci sectors."""
import unittest
from random import Random
from fractions import Fraction as F
from research.toe.auxiliary_g_schur import (
    symmetry_bilinear,diagonal_vector_hessian, inverse,mm,trace
)
from research.toe.form_sector_principal import (
    linearized_ricci,metric_tensor_mode,tt_vector_coefficient,
    background_denominators)

class AuxiliarySchurTests(unittest.TestCase):
    def test_scalar_elimination(self):
        for theta in (F(1),F(2,3),F(11,8)):
            for du,dv in ((F(1),F(2)),(F(-2,3),F(1,9)),(0,0)):
                r=symmetry_bilinear(((theta,),),((du,),),((dv,),))
                self.assertEqual(r['direct'],du*dv/theta**2)

    def test_matrix_diagonal_schur(self):
        rng=Random(511)
        for _ in range(160):
            t=[F(rng.randrange(1,12),10) for i in range(4)]
            th=tuple(tuple((t[i] if i==j else F()) for j in range(4)) for i in range(4))
            a=tuple(tuple(F(rng.randrange(-4,5),10) for j in range(4)) for i in range(4))
            b=tuple(tuple(F(rng.randrange(-4,5),10) for j in range(4)) for i in range(4))
            r=symmetry_bilinear(th,a,b)
            self.assertEqual(r['direct'],sum((a[i][j]*b[j][i]/(t[i]*t[j]) for i in range(4) for j in range(4)),F()))

    def test_linear_response_dG_is_exact_inverse_variation(self):
        theta=((F(2),F()),(F(),F(3)))
        d=((F(1),F(2)),(F(2),F(0)))
        r=symmetry_bilinear(theta,d,d)
        self.assertEqual(r['stationary_dG1'],((F(-1,4),F(-1,3)),(F(-1,3),F())))

    def test_vector_tt_schur_matches_4x4_direct(self):
        A,B,beta=F(2,5),F(1),F(1,100)
        th=background_denominators(A,B,beta)
        for w in (-2,-1,0,1,2,F(1,2)):
            dr,_=linearized_ricci((w,0,0,1),metric_tensor_mode(False))
            actual=diagonal_vector_hessian(th[1],th[2],dr,beta)
            coeff=tt_vector_coefficient(A=A,Bcurv=B,beta=beta,sigma1=1)
            self.assertEqual(actual,coeff*(F(w)**2-1)**2)

    def test_vector_tt_cross_pol_schur(self):
        A,B,beta=F(2,5),F(1),F(1,100)
        th=background_denominators(A,B,beta)
        dr,_=linearized_ricci((F(2),0,0,1),metric_tensor_mode(True))
        x=diagonal_vector_hessian(th[1],th[2],dr,beta)
        y=diagonal_vector_hessian(th[1],th[2],linearized_ricci((F(2),0,0,1),metric_tensor_mode(False))[0],beta)
        self.assertEqual(x,y)

    def test_noninvertible_background_rejected(self):
        with self.assertRaises(ValueError):inverse(((0,0),(0,0)))
        with self.assertRaises(ValueError):symmetry_bilinear(((1,0),(0,0)),((0,0),(0,0)),((0,0),(0,0)))

if __name__=='__main__':unittest.main()
