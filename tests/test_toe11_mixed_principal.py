"""Exact rational tests of the homogeneous mixed principal-jet Hessian."""
import math
import random
import unittest
from fractions import Fraction as Q

from research.toe.mixed_principal import (
    partial_jet, two_flavor_determinant, det, quad, example,
)
from research.toe.lorentz_bivector import source_block


def mk(E=(2,Q(1001,1000)), B=(1,0), **kw):
    params=dict(A=Q(2,5),Bcurv=1,alpha=Q(3,500),
                beta=Q(1,100),sigma=Q(1,100))
    params.update(kw)
    return partial_jet(E,B,**params)


class MixedPrincipalExact(unittest.TestCase):
    def test_curvature_coefficient(self):
        x=mk()
        self.assertEqual(x.curvature_entry,12*x.sigma*x.beta**2*x.theta_b**2/x.determinant**2)

    def test_mixed_entry_nonzero(self):
        x=mk()
        self.assertTrue(any(v!=0 for v in x.mixed_entries))
        self.assertEqual(x.mixed_entries,tuple(12*x.sigma*x.alpha*x.beta*x.theta_b*v/x.determinant**2
                                               for v in x.v))

    def test_independent_symmetric_hessian(self):
        x=mk()
        for i in range(3):
            for j in range(3):self.assertEqual(x.full_hessian[i][j],x.full_hessian[j][i])

    def test_kinetic_minor_factorization_two_flavors(self):
        r=random.Random(2411101)
        for _ in range(90):
            E=tuple(Q(r.randint(-10,10),20) for i in range(2))
            B=tuple(Q(r.randint(-10,10),20) for i in range(2))
            p=mk(E,B,A=Q(r.randint(-5,9),10), Bcurv=Q(r.randint(0,8),10),
                 alpha=Q(r.randint(1,5),100), beta=Q(r.randint(1,5),100),
                 sigma=Q(r.randint(1,5),100))
            self.assertEqual(det(p.full_hessian),p.factorized_determinant)
            self.assertEqual(two_flavor_determinant(p),p.factorized_determinant)
            self.assertTrue(p.factorized_determinant>0)

    def test_three_flavors_rank_one_schur(self):
        r=random.Random(11023)
        for _ in range(30):
            E=[Q(r.randint(-3,3),10) for i in range(3)]
            B=[Q(r.randint(-3,3),10) for i in range(3)]
            x=mk(E,B,alpha=Q(1,30),sigma=Q(1,40))
            self.assertEqual(det(x.full_hessian),x.curvature_entry*det(x.gauge_base))
            self.assertTrue(x.factorized_determinant>0)

    def test_kinetic_sum_of_squares(self):
        r=random.Random(10570)
        for _ in range(180):
            E=[Q(r.randint(-5,5),10) for i in range(2)]
            B=[Q(r.randint(-5,5),10) for i in range(2)]
            p=mk(E,B,alpha=Q(1,30),sigma=Q(1,100))
            da=Q(r.randint(-5,5),8)
            de=[Q(r.randint(-5,5),8) for i in range(2)]
            self.assertEqual(quad(p.full_hessian,(da,*de)),p.squares(da,de))
            if da or any(de):
                self.assertGreater(p.squares(da,de),0)

    def test_lower_bound_by_gauge_kinetic(self):
        x=mk()
        for da in (-1,0,1):
            for dx in (-1,0,1):
                for dy in (-1,0,1):
                    self.assertGreaterEqual(x.squares(da,(dx,dy)),3*(dx*dx+dy*dy))

    def test_spectral_vs_jet_independence(self):
        spectral=[]
        for eps in (Q(-1,1000), Q(), Q(1,1000)):
            x=mk((2,1+eps),(1,0))
            self.assertTrue(x.proven_positive_jet)
            self.assertGreater(x.full_determinant,0)
            block=source_block((2,1+eps),(1,0),H=1,Hdot=Q(-3,5),
                               alpha=Q(3,500),beta=Q(1,100))
            self.assertEqual(block.discriminant,x.discriminant)
            self.assertEqual(block.exact_positive_real,x.positive_real_spectral)
            spectral.append(x.positive_real_spectral)
        self.assertEqual(spectral,[False,False,True])

    def test_hessian_exists_at_defective_krein_boundary(self):
        x=mk((2,1),(1,0))
        self.assertEqual(x.discriminant,0)
        self.assertGreater(x.curvature_entry,0)
        self.assertGreater(x.full_determinant,0)
        self.assertFalse(x.positive_real_spectral)

    def test_sigma_zero_gauge_only(self):
        x=mk(sigma=0)
        self.assertEqual(x.curvature_entry,0)
        self.assertEqual(x.full_determinant,0)
        self.assertEqual(x.mixed_entries,(0,0))
        self.assertEqual(x.gauge_hessian,((3,0),(0,3)))

    def test_pure_magnetic_direction_parallel(self):
        x=mk((Q(1,10),Q(1,11)),(3,0))
        r=3+6*x.sigma*x.alpha*x.base_magnetic/x.determinant
        self.assertEqual(quad(x.gauge_base,(1,0)),r)
        p=3+6*x.sigma*x.alpha*x.theta_b/x.determinant
        self.assertEqual(quad(x.gauge_base,(0,1)),p)

    def test_kinetic_quadratic_stays_positive_complex_region(self):
        x=mk((2,Q(999,1000)),(1,0))
        self.assertLess(x.discriminant,0)
        self.assertTrue(x.proven_positive_jet)
        self.assertGreater(quad(x.full_hessian,(2,-1,3)),0)

    def test_no_physical_claim_from_log_determinant(self):
        x=mk((2,Q(999,1000)),(1,0))
        self.assertGreater(x.determinant,0)
        self.assertFalse(x.positive_real_spectral)

    def test_invariance_of_gauge_flavor_frame(self):
        R=((Q(3,5),-Q(4,5)),(Q(4,5),Q(3,5)))
        E=(Q(1,3),Q(2,7)); B=(Q(4,13),Q(-1,11))
        rotate=lambda v:tuple(sum(R[i][j]*v[j] for j in range(2)) for i in range(2))
        x=mk(E,B); y=mk(rotate(E),rotate(B))
        self.assertEqual((x.theta_e,x.theta_b,x.determinant,x.discriminant),
                         (y.theta_e,y.theta_b,y.determinant,y.discriminant))
        self.assertEqual(x.full_determinant,y.full_determinant)

    def test_sample_certificate(self):
        x=example()
        self.assertEqual(x['schema'],'mathcan.toe11.partial_jet.v1')
        self.assertTrue(x['cases']['real']['positive_real_spectrum'])
        self.assertFalse(x['cases']['complex']['positive_real_spectrum'])
        self.assertTrue(all(v['positive_jet'] for v in x['cases'].values()))

    def test_malformed_shape(self):
        for E,B in (((),()),((1,),(1,2))):
            with self.assertRaises(ValueError):mk(E,B)
        with self.assertRaises(ValueError):mk(sigma=-1)
        with self.assertRaises(ValueError):mk(alpha=0)
        with self.assertRaises(ValueError):mk(beta=0)
        with self.assertRaises(ValueError):mk((8,9),(0,0),alpha=1,beta=Q(1,100))

    def test_squares_bad_vector(self):
        with self.assertRaises(ValueError):mk().squares(1,(1,))

    def test_only_two_flavor_closed_product(self):
        with self.assertRaises(ValueError):two_flavor_determinant(mk((1,2,3),(0,0,0)))

    def test_independent_finite_differences(self):
        # The formula is a true Hessian of the declared *logarithmic action*.
        E=(.24,.39); B=(.14,.22); alpha=.03; beta=.02; sig=.07; A=.22;Bc=.17
        def energy(v):
            a,x,y=v
            e=x*x+y*y; b=B[0]**2+B[1]**2;c=x*B[0]+y*B[1]
            D=(1-alpha*e-2*beta*a)*(1+alpha*b-2*beta*Bc)+alpha**2*c*c
            return 1.5*(e-b)-3*sig*math.log(D)
        x0=(A,*E);h=1e-4
        r=partial_jet(tuple(Q(str(z)) for z in E),tuple(Q(str(z)) for z in B),
                      A=Q(str(A)),Bcurv=Q(str(Bc)),alpha=Q(str(alpha)),
                      beta=Q(str(beta)),sigma=Q(str(sig)))
        v0=energy(x0)
        for i in range(3):
            def mv(changes):return tuple(x0[j]+changes.get(j,0) for j in range(3))
            second=(energy(mv({i:h}))-2*v0+energy(mv({i:-h})))/h**2
            self.assertAlmostEqual(float(r.full_hessian[i][i]),second,delta=4e-7)
            for j in range(i):
                mixed=(energy(mv({i:h,j:h}))-energy(mv({i:h,j:-h}))-
                       energy(mv({i:-h,j:h}))+energy(mv({i:-h,j:-h})))/(4*h*h)
                self.assertAlmostEqual(float(r.full_hessian[i][j]),mixed,delta=4e-7)

if __name__=='__main__':unittest.main()
