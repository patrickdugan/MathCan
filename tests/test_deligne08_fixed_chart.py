"""Exact finite-field regression checks for DEL-08 source geometry."""
from itertools import product
import random
import unittest

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del08_oracle import (
    affine_hyperplane,
    normalize_hyperplane,
    check_normalized_zero_set,
    conic_good,
    conic_singular,
    count_conic_good_parameters,
    frobenius_gap,
    bipartite_quadratic,
    bipartite_partial_x,
    check_bipartite_level,
    tangent_line_restriction_mutant,
    graph_nonimmersion_collision,
)
from research.deligne_sign_audit.del08_verify_tasks import verify


class Deligne08FixedCoefficientTests(unittest.TestCase):
    def test_all_80_mutation_labels(self):
        self.assertEqual(sum(verify().values()),80)

    def test_normalization_on_every_small_field(self):
        rng=random.Random(261100798)
        for name,f in FIELDS.items():
            for _ in range(75):
                a=tuple(rng.randrange(f.q) for _ in range(3))
                z=tuple(rng.randrange(f.q) for _ in range(3))
                last=rng.randrange(1,f.q)
                c=rng.randrange(f.q)
                fixed=rng.randrange(f.q)
                receipt=check_normalized_zero_set(
                    f,a,last,c,fixed,z)
                self.assertEqual(receipt,(True,True),(name,receipt))

    def test_zero_last_coefficient_must_be_rejected(self):
        for name,f in FIELDS.items():
            with self.assertRaisesRegex(ValueError,"nonzero"):
                normalize_hyperplane(f,(1,0),0,1)

    def test_affine_conic_discriminant_exact(self):
        for name,f in FIELDS.items():
            with self.subTest(field=name):
                good,bad=count_conic_good_parameters(f)
                self.assertEqual(good,f.q*f.q*(f.q-1))
                self.assertEqual(bad,f.q*f.q)

    def test_finite_extension_needed_for_dense_open_points(self):
        for small,large in (("F2","F4"),("F3","F9"),("F5","F25")):
            f0,f1=FIELDS[small],FIELDS[large]
            allzero,count,outside=frobenius_gap(f1)
            self.assertTrue(allzero)
            self.assertEqual(count,f1.q-f1.p)
            self.assertTrue(outside)
            self.assertEqual(count,len(outside))
            self.assertTrue(all(f0.sub(f0.pow(x,f0.p),x)==0
                                for x in range(f0.q)))

    def test_bipartite_euler_jacobian_all_characteristics(self):
        rng=random.Random(261100799)
        for name in ("F2","F3","F4","F5","F8","F9","F25"):
            f=FIELDS[name]
            for _ in range(100):
                A=[[rng.randrange(f.q) for _ in range(3)]
                   for _ in range(2)]
                x=[rng.randrange(f.q) for _ in range(2)]
                y=[rng.randrange(f.q) for _ in range(3)]
                c=rng.randrange(1,f.q)
                self.assertTrue(check_bipartite_level(f,A,x,y,c))

    def test_path_phase_nonzero_constant_is_ambient_regular(self):
        for name,k_max in (("F2",7),("F3",6),("F4",5),
                           ("F5",4),("F9",3),("F25",2)):
            f=FIELDS[name]
            for k in range(2,k_max+1):
                for xs in product(range(f.q),repeat=k):
                    Q=0
                    for i in range(k-1):
                        Q=f.add(Q,f.mul(xs[i],xs[i+1]))
                    if f.add(Q,1)!=0:
                        continue
                    grad=[]
                    for i in range(k):
                        g=0
                        if i: g=f.add(g,xs[i-1])
                        if i+1<k: g=f.add(g,xs[i+1])
                        grad.append(g)
                    self.assertTrue(any(x!=0 for x in grad),
                                    (name,k,xs))

    def test_ambient_smoothness_does_not_transfer_to_tangent_line(self):
        for name in ("F2","F3","F4","F5","F9","F25"):
            f=FIELDS[name]
            self.assertEqual(tangent_line_restriction_mutant(f),
                             (True,True,True))

    def test_nonembedding_if_original_coordinates_fail(self):
        for name,f in FIELDS.items():
            self.assertEqual(graph_nonimmersion_collision(f),
                             (True,True),(name,f.q))

    def test_fixed_chart_conic_preserves_nonempty_good_parameters(self):
        for name,f in FIELDS.items():
            good=0
            for a,b,c in product(range(f.q),repeat=3):
                good += conic_good(f,a,b,c)
            self.assertEqual(good,f.q*f.q*(f.q-1))
            self.assertGreater(good,0)

    def test_tangent_incidence_arithmetic_only(self):
        for D in range(1,25):
            for M in range(D+1,D+8):
                self.assertEqual(D+(M-D-1),M-1)
                self.assertLess(M-1,M)


if __name__=="__main__":
    unittest.main()
