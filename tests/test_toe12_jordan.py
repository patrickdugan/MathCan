"""TOE-12 exact rational Jordan, gauge and hypothetical-completion checks."""
from dataclasses import replace
from fractions import Fraction as F
from random import Random
import unittest

from research.toe.wave_principal import construct_symbol,evaluate_polynomial
from research.toe.jordan_principal import (
    Polynomial,exact_example,polynomial,jordan_certificate,determinant_completion,
    eye,zero,mm,add,rank,charpoly,diag_shift,wedge_matrix,wedge,
    gauge_slice,lorenz_gauss,bare_null_cone_physical_basis,reference_experiment,
)

class JordanTests(unittest.TestCase):
    def setUp(self):
        self.w=exact_example()
        self.p=polynomial(self.w)
        self.c=self.p.companion()

    def test_source_reconstruction_and_factors(self):
        r=self.w.doubled_gravity_root;s=self.w.remaining_root()
        self.assertEqual((self.p.r0,self.p.r2,self.p.r4),self.w.rr)
        self.assertEqual((self.p.m1,self.p.m3),self.w.rf)
        self.assertEqual((self.p.f0,self.p.f2),self.w.ff)
        self.assertEqual(self.p.r2,-2*self.p.r4*r)
        self.assertEqual(self.p.r0,self.p.r4*r*r)
        self.assertEqual(self.p.m1,-self.p.m3*r)
        det=self.p.determinant()
        for x in (F(),F(1,10),r,s,F(2),F(7,3)):
            expected=(x-r)**2*(self.p.r4*self.p.f2-self.p.m3**2)*(x-s)
            self.assertEqual(evaluate_polynomial(det,x),expected)

    def test_companion_characteristic_independent(self):
        self.assertEqual(charpoly(self.c),self.p.expected_companion_polynomial())
        self.assertEqual(charpoly(self.c)[1::2],(F(),F(),F()))

    def test_repeated_root_and_positive_speeds(self):
        c=jordan_certificate(self.w)
        self.assertEqual(c['root_r'],'480993997/493000000')
        self.assertEqual(c['nonzero_nilpotent_rank'],2)
        self.assertEqual(c['eigenmatrix_rank_at_r'],1)
        self.assertTrue(c['nilpotent_square_zero'])
        self.assertFalse(c['full_theory_hyperbolicity_verified'])

    def test_jordan_nontrivial_nilpotent(self):
        r=self.w.doubled_gravity_root;s=self.w.remaining_root()
        a=diag_shift(mm(self.c,self.c),-r)
        b=diag_shift(mm(self.c,self.c),-s)
        N=mm(a,b)
        self.assertNotEqual(N,zero(6))
        self.assertEqual(mm(N,N),zero(6))
        self.assertEqual(rank(N),2)
        self.assertEqual(mm(a,b),mm(b,a))

    def test_at_double_root_matrix_has_one_eigenvector(self):
        r=self.w.doubled_gravity_root
        rr=self.p.r4*r*r+self.p.r2*r+self.p.r0
        rf=self.p.m3*r+self.p.m1
        ff=self.p.f2*r+self.p.f0
        self.assertEqual((rr,rf),(0,0))
        self.assertNotEqual(ff,0)
        self.assertEqual(rank(((rr,rf),(rf,ff))),1)

    def test_derived_system_respects_two_original_odes(self):
        rng=Random(7112026)
        C=self.c;p=self.p
        for _ in range(50):
            x=tuple(F(rng.randint(-10,10),rng.randint(1,13)) for j in range(6))
            v=tuple(sum((a*b for a,b in zip(row,x)),F()) for row in C)
            a=tuple(sum((y*b for y,b in zip(row,v)),F()) for row in C)
            self.assertEqual(p.m3*x[3]+p.m1*x[1]+p.f2*v[5]+p.f0*x[4],0)
            self.assertEqual(p.r4*v[3]+p.r2*x[2]+p.r0*x[0]+p.m3*a[5]+p.m1*x[5],0)

    def test_jordan_certificate_rejects_nonpositive_root(self):
        bad=replace(self.w,remaining_linear_factor=(F(1),F(1)))
        with self.assertRaises(ValueError):jordan_certificate(bad)

    def test_leading_pencil_degenerate_rejected(self):
        with self.assertRaises(ValueError):replace(self.p,f2=F()).companion()
        with self.assertRaises(ValueError):replace(self.p,r4=self.p.m3**2/self.p.f2).companion()

    def test_faddeev_leverrier_hand_example(self):
        self.assertEqual(charpoly(((F(1),F(2)),(F(3),F(4)))),(F(1),F(-5),F(-2)))
        self.assertEqual(charpoly(((F(2),F()),(F(),F(3)))),(F(1),F(-5),F(6)))

    def test_completion_three_distinct_positive_roots(self):
        q=determinant_completion(self.w)
        self.assertTrue(q['three_distinct_positive_x_roots'])
        a,b,c=map(F,q['Q_at_brackets'])
        self.assertGreater(a,0);self.assertLess(b,0);self.assertGreater(c,0)
        self.assertLess(F(q['left_interval'][0]),F(q['old_root']))
        self.assertGreater(F(q['old_third_root']),F(q['old_root']))

    def test_completion_split_source_is_explicitly_hypothetical(self):
        q=determinant_completion(self.w,10000)
        self.assertFalse(q['full_physics_completion'])
        self.assertEqual(F(q['epsilon']),self.p.r4/10000)

    def test_completion_invalid_scale_rejected(self):
        for scale in (0,-1,1.5,True):
            with self.assertRaises(ValueError):determinant_completion(self.w,scale)

    def test_companion_perturbation_charpoly_exact(self):
        r=self.w.doubled_gravity_root
        for scale in (1000,10000,100000):
            eps=self.p.r4/scale
            p=replace(self.p,r2=self.p.r2+eps,r0=self.p.r0-eps*r)
            self.assertEqual(charpoly(p.companion()),p.expected_companion_polynomial())

    def test_random_polynomial_companions(self):
        rng=Random(12211)
        for _ in range(30):
            a=F(rng.randint(1,8));f=F(rng.randint(1,8));b=F(rng.randint(-2,2))
            p=Polynomial(a,F(rng.randint(-9,9)),F(rng.randint(-9,9)),
                         b,F(rng.randint(-9,9)),f,F(rng.randint(-9,9)))
            if a*f==b*b:continue
            self.assertEqual(charpoly(p.companion()),p.expected_companion_polynomial())


class BareGaugeTests(unittest.TestCase):
    def test_pure_gauge_wedge_zero(self):
        rng=Random(8812)
        for _ in range(120):
            xi=tuple(F(rng.randint(-5,5)) for j in range(4))
            k=F(rng.randint(-4,4))
            self.assertEqual(wedge(xi,tuple(k*z for z in xi)),(0,)*6)

    def test_exact_rank_for_generic_nonzero_covectors(self):
        rng=Random(2208)
        for _ in range(220):
            xi=tuple(F(rng.randint(-3,3),rng.randint(1,9)) for j in range(4))
            if any(xi):self.assertEqual(rank(wedge_matrix(xi)),3)

    def test_quotient_keeps_same_field_strength(self):
        rng=Random(7718)
        for _ in range(180):
            xi=tuple(F(rng.randint(-7,7),rng.randint(1,7)) for j in range(4))
            if not any(xi):continue
            a=tuple(F(rng.randint(-7,7),rng.randint(1,7)) for j in range(4))
            rep=gauge_slice(xi,a)
            self.assertEqual(rep['field_strength'],wedge(xi,a))
            self.assertEqual(rep['quotient_rank'],3)
            self.assertEqual(rep['representative'][rep['pivot']],0)

    def test_gauge_invariance_of_bare_gauss(self):
        rng=Random(22081)
        for _ in range(180):
            xi=tuple(F(rng.randint(-3,3)) for j in range(4))
            a=tuple(F(rng.randint(-3,3)) for j in range(4))
            k=F(rng.randint(-3,3))
            shifted=tuple(u+k*v for u,v in zip(a,xi))
            self.assertEqual(lorenz_gauss(xi,a),lorenz_gauss(xi,shifted))

    def test_null_waves_have_two_transverse_bare_modes(self):
        report=bare_null_cone_physical_basis()
        self.assertEqual(report['bare_total_transverse_modes'],12)
        self.assertFalse(report['nonminimal_gauge_constraints_derived'])
        xi=(1,0,0,1)
        for a in ((0,1,0,0),(0,0,1,0),(0,0,0,0)):
            self.assertEqual(lorenz_gauss(xi,a),(F(),)*4)
        self.assertNotEqual(lorenz_gauss(xi,(0,0,0,1)),(F(),)*4)

    def test_gauge_slice_rejects_zero_wave(self):
        with self.assertRaises(ValueError):gauge_slice((0,0,0,0),(1,0,0,0))
        with self.assertRaises(ValueError):wedge_matrix((1,0,0))
        with self.assertRaises(ValueError):wedge((1,0,0,0),(1,0,0))

    def test_wave_null_per_color(self):
        xi=(1,0,0,1)
        self.assertEqual(rank(wedge_matrix(xi)),3)
        self.assertEqual(wedge(xi,xi),(F(),)*6)
        self.assertEqual(gauge_slice(xi,xi)['representative'],(F(),)*4)

    def test_reference_includes_separate_full_theory_gate(self):
        out=reference_experiment()
        self.assertIs(out['jordan']['full_theory_hyperbolicity_verified'],False)
        self.assertIs(out['bare_yang_mills_gauge']['nonminimal_gauge_constraints_derived'],False)

if __name__=='__main__':unittest.main()
