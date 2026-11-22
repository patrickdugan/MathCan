"""DEL-11 exact tests of the characteristic-free bilinear discriminant."""
from itertools import product
import random
import unittest

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del11_oracle import (
    bilinear_equation, bad_discriminant, formal_gradient,
    critical_point, brute_force_critical_points,
    count_bad_parameters, constant_one_good_parameter,
    wrong_plus_discriminant, cross_coupled_discriminant,
    solve_katz_linear_open,
)
from research.deligne_sign_audit.del11_verify_tasks import verify


class Deligne11BilinearBadLocusTests(unittest.TestCase):
    def test_full_96_case_mutation_oracle(self):
        self.assertEqual(sum(verify().values()),96)

    def test_complete_square_formula_exact_over_every_field(self):
        rng=random.Random(261100811)
        for name,f in FIELDS.items():
            for n in (1,2,3):
                for _ in range(50):
                    a,b,x,y=[tuple(rng.randrange(f.q) for i in range(n))
                             for _ in range(4)]
                    c=rng.randrange(f.q)
                    original=bilinear_equation(f,a,b,c,x,y)
                    completed=c
                    for i in range(n):
                        sq=f.mul(f.add(x[i],b[i]),f.add(y[i],a[i]))
                        completed=f.add(completed,
                                        f.sub(sq,f.mul(a[i],b[i])))
                    self.assertEqual(original,completed,(name,n,a,b,c))

    def test_critical_iff_discriminant_for_random_coefficients(self):
        rng=random.Random(261100812)
        for name,f in FIELDS.items():
            for n in (0,1,2,3):
                for _ in range(35):
                    a=tuple(rng.randrange(f.q) for _ in range(n))
                    b=tuple(rng.randrange(f.q) for _ in range(n))
                    c=rng.randrange(f.q)
                    x,y,phase=critical_point(f,a,b,c)
                    self.assertEqual(phase,bad_discriminant(f,a,b,c))
                    if f.q**(2*n)<=400:
                        points=brute_force_critical_points(f,a,b,c)
                        self.assertEqual(len(points),
                            int(phase==0),(name,n,a,b,c))

    def test_critical_locus_count_formula(self):
        for name,n in (
            ("F2",0),("F2",1),("F2",2),("F2",3),
            ("F3",1),("F3",2),("F4",1),("F4",2),
            ("F5",1),("F8",1),("F9",1),("F16",1),
        ):
            f=FIELDS[name]
            good,bad=count_bad_parameters(f,n)
            self.assertEqual(bad,f.q**(2*n))
            self.assertEqual(good,f.q**(2*n)*(f.q-1))

    def test_all_constant_one_parameters_are_nonsingular(self):
        for name,f in FIELDS.items():
            for n in (0,1,2,3,6):
                a,b,c,delta=constant_one_good_parameter(f,n)
                self.assertEqual(c,1)
                self.assertEqual(delta,1)
                self.assertNotEqual(bad_discriminant(f,a,b,c),0)

    def test_actual_gradient_nonvanishing_on_good_hypersurface(self):
        for name,n in (("F2",2),("F3",2),("F4",2),("F5",1)):
            f=FIELDS[name]
            a=(1,)*n
            b=(0,)*n
            c=1
            self.assertNotEqual(bad_discriminant(f,a,b,c),0)
            for x in product(range(f.q),repeat=n):
                for y in product(range(f.q),repeat=n):
                    if bilinear_equation(f,a,b,c,x,y)!=0:
                        continue
                    dy,dx=formal_gradient(f,a,b,x,y)
                    self.assertTrue(any(dy+dx),(name,n,x,y))

    def test_wrong_discriminant_sign_in_odd_characteristic(self):
        for name in ("F3","F5","F9","F25","F27"):
            f=FIELDS[name]
            a,b=(1,),(1,)
            c=f.neg(1)
            self.assertEqual(wrong_plus_discriminant(f,a,b,c),0)
            self.assertNotEqual(bad_discriminant(f,a,b,c),0)

    def test_cross_coupling_mutant(self):
        for name,f in FIELDS.items():
            a,b,c=(1,0),(1,0),0
            self.assertEqual(cross_coupled_discriminant(f,a,b,c),0)
            self.assertNotEqual(bad_discriminant(f,a,b,c),0)

    def test_good_hyperbola_and_example_katz_linear_open(self):
        for name,f in FIELDS.items():
            for n in (0,1,2,3):
                witness=solve_katz_linear_open(f,n)
                self.assertIsNotNone(witness)
                a,b,c=witness
                self.assertNotEqual(c,0)
                self.assertNotEqual(bad_discriminant(f,a,b,c),0)

    def test_char_two_does_not_require_division_by_two(self):
        for name in ("F2","F4","F8","F16"):
            f=FIELDS[name]
            a,b,c=(1,0),(0,1),1
            self.assertEqual(bad_discriminant(f,a,b,c),1)
            for x in product(range(f.q),repeat=2):
                for y in product(range(f.q),repeat=2):
                    if bilinear_equation(f,a,b,c,x,y)==0:
                        dy,dx=formal_gradient(f,a,b,x,y)
                        self.assertTrue(any(dy+dx))

    def test_singular_gradient_witness_is_unique(self):
        for name,n in (("F2",3),("F3",2),("F4",2),
                       ("F5",1),("F9",1)):
            f=FIELDS[name]
            a=tuple(i%f.q for i in range(n))
            b=tuple((i+1)%f.q for i in range(n))
            c=0
            for ai,bi in zip(a,b):
                c=f.add(c,f.mul(ai,bi))
            points=brute_force_critical_points(f,a,b,c)
            self.assertEqual(len(points),1)
            self.assertEqual(points[0][0],tuple(f.neg(v) for v in b))
            self.assertEqual(points[0][1],tuple(f.neg(v) for v in a))

    def test_invalid_field_vectors_rejected(self):
        f=FIELDS["F4"]
        with self.assertRaisesRegex(ValueError,"dimensions"):
            bad_discriminant(f,(1,0),(2,),0)
        with self.assertRaisesRegex(ValueError,"out of range"):
            bad_discriminant(f,(4,),(0,),0)


if __name__=="__main__":
    unittest.main()
