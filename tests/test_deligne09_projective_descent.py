"""DEL-09 exact tests for projective graph charts and finite parameter descent."""
import random
import unittest

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del09_oracle import (
    common_subfield_degree, polynomial_open_frobenius_gap,
    projective_chart_graph, projective_graph_fibers,
    injective_graph_certificate, omit_base_coordinate_mutant,
    affine_chart_contains, affine_normalization,
    source_geometry_tangency_mutant,
)
from research.deligne_sign_audit.del09_verify_tasks import verify


class Deligne09ProjectiveDescentTests(unittest.TestCase):
    def test_all_96_task_labels(self):
        self.assertEqual(sum(verify().values()),96)

    def test_common_field_contains_arbitrary_parameter_tuples(self):
        rng=random.Random(261100800)
        for name,field in FIELDS.items():
            for n in (0,1,2,3,5,8):
                for _ in range(10):
                    vals=[rng.randrange(field.q) for _ in range(n)]
                    e,order=common_subfield_degree(field,vals)
                    self.assertEqual(field.degree%e,0)
                    self.assertEqual(order,field.p**e)
                    self.assertTrue(
                        all(field.pow(x,field.p**e)==x for x in vals),
                        (name,vals,e))

    def test_primitive_generator_requires_full_extension(self):
        for name in ("F4","F8","F9","F16","F25","F27"):
            field=FIELDS[name]
            degree,order=common_subfield_degree(field,[field.p])
            self.assertEqual(degree,field.degree,name)
            self.assertEqual(order,field.q)

    def test_intermediate_F4_inside_F16(self):
        field=FIELDS["F16"]
        proper=[x for x in range(field.p,field.q)
                if field.pow(x,4)==x]
        self.assertEqual(len(proper),2)
        for x in proper:
            self.assertEqual(common_subfield_degree(field,[x]),(2,4))
            self.assertEqual(common_subfield_degree(field,[x,1]),(2,4))
            self.assertEqual(common_subfield_degree(field,[x,field.p]),(4,16))

    def test_frobenius_gap_requires_extension_points(self):
        for name in ("F4","F9","F25"):
            f=FIELDS[name]
            base,extension=polynomial_open_frobenius_gap(f)
            self.assertEqual(len(base),f.p)
            self.assertEqual(len(extension),f.q-f.p)
            self.assertTrue(extension)
            self.assertTrue(all(x>=f.p for x in extension))
            self.assertFalse(any(x in base for x in extension))

    def test_graph_then_projective_chart_point_fibers(self):
        rng=random.Random(261100801)
        for name in FIELDS:
            f=FIELDS[name]
            for _ in range(9):
                a,b=rng.randrange(f.q),rng.randrange(f.q)
                count,max_fiber=injective_graph_certificate(f,a,b)
                self.assertEqual((count,max_fiber),(f.q,1))
                points=projective_chart_graph(f,a,b)
                self.assertTrue(all(point[0]==1 for point in points))
                self.assertEqual(len(set(points)),f.q)

    def test_wrong_chart_at_infinity(self):
        for name,field in FIELDS.items():
            for x in range(min(field.q,6)):
                self.assertFalse(affine_chart_contains((0,1,x)))
                self.assertTrue(affine_chart_contains((1,0,x)))
                self.assertTrue(affine_chart_contains((field.p,0,x)))
                with self.assertRaises(ValueError):
                    affine_chart_contains(())

    def test_collapsed_base_coordinate_is_not_an_embedding(self):
        for name in ("F2","F3","F5"):
            f=FIELDS[name]
            self.assertEqual(omit_base_coordinate_mutant(f),(1,f.p))
            self.assertGreater(f.p,1)

    def test_normalization_requires_nonzero_coefficient(self):
        for name,f in FIELDS.items():
            with self.assertRaisesRegex(ValueError,"nonzero"):
                affine_normalization(f,(1,2%f.p),0)
            for lam in range(1,f.q):
                coeffs=(0,1,lam)
                result=affine_normalization(f,coeffs,lam)
                self.assertEqual(result[-1],1)

    def test_ambient_smoothness_does_not_imply_restricted_smoothness(self):
        for name,f in FIELDS.items():
            self.assertEqual(source_geometry_tangency_mutant(f),
                             (True,True,True,True))

    def test_empty_coefficient_tuple_stays_in_base_field(self):
        for name,f in FIELDS.items():
            self.assertEqual(common_subfield_degree(f,[]),(1,f.p))
            self.assertEqual(common_subfield_degree(f,[0,1]),(1,f.p))

    def test_reject_out_of_range_extension_element(self):
        for name,f in FIELDS.items():
            with self.assertRaisesRegex(ValueError,"outside"):
                common_subfield_degree(f,[f.q])


if __name__=="__main__":
    unittest.main()
