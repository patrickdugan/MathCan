"""DEL-14 exact iff tests for the global conic Jacobian ideal."""
from itertools import product
import random
import unittest

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del12_oracle import evaluate, conic_polynomial
from research.deligne_sign_audit.del13_oracle import (
    conic_bezout, conic_unit_certificate,
    singular_ideal_obstruction, field_oracle,
)
from research.deligne_sign_audit.del14_verify_tasks import verify


class Deligne14SharpJacobianTests(unittest.TestCase):
    def test_complete_72_task_oracle(self):
        self.assertEqual(sum(verify().values()),72)

    def test_unit_iff_delta_nonzero_over_all_small_fields(self):
        for name in ("F2","F3","F4","F5"):
            f=FIELDS[name]
            for a,b,c in product(range(f.q),repeat=3):
                receipt=field_oracle(name,a,b,c)
                self.assertTrue(receipt["identity"])
                self.assertEqual(receipt["unit_if_nonzero"],
                                 receipt["delta"]!=0)
                self.assertEqual(receipt["singular_if_zero"],
                                 receipt["delta"]==0)

    def test_random_extension_field_iff(self):
        rng=random.Random(261100814)
        for name,f in FIELDS.items():
            for _ in range(90):
                a,b,c=(rng.randrange(f.q) for _ in range(3))
                receipt=field_oracle(name,a,b,c)
                self.assertEqual(receipt["unit_if_nonzero"],
                                 receipt["delta"]!=0)
                self.assertEqual(receipt["singular_if_zero"],
                                 receipt["delta"]==0)

    def test_proper_ideal_has_explicit_evaluation_kernel(self):
        for name,f in FIELDS.items():
            for a in range(min(f.q,5)):
                for b in range(min(f.q,5)):
                    c=f.mul(a,b)
                    obstruction=singular_ideal_obstruction(f,a,b,c)
                    self.assertEqual(obstruction["generator_evaluations"],(0,0,0))
                    self.assertIsNone(conic_unit_certificate(f,a,b,c))
                    self.assertEqual(obstruction["singular_point"],
                                     (f.neg(b),f.neg(a)))

    def test_nonzero_discriminant_has_explicit_inverse(self):
        for name,f in FIELDS.items():
            for a in range(min(f.q,4)):
                for b in range(min(f.q,4)):
                    c=f.add(f.mul(a,b),1)
                    certificate=conic_unit_certificate(f,a,b,c)
                    self.assertIsNotNone(certificate)
                    self.assertTrue(certificate["unit_identity"])
                    self.assertEqual(f.mul(certificate["delta"],
                                           certificate["inverse"]),1)

    def test_shifted_singularity_is_not_at_origin(self):
        for name,f in FIELDS.items():
            a,b,c=1,1,1
            self.assertNotEqual(evaluate(f,conic_polynomial(f,a,b,c),0,0),0)
            obstruction=singular_ideal_obstruction(f,a,b,c)
            self.assertTrue(obstruction["all_generators_zero"])
            self.assertEqual(obstruction["singular_point"],(f.neg(1),f.neg(1)))

    def test_proper_ideal_cannot_contain_unit(self):
        for name,f in FIELDS.items():
            for a,b in ((0,0),(1,0),(0,1),(1,1)):
                c=f.mul(a,b)
                obstruction=singular_ideal_obstruction(f,a,b,c)
                # All generators vanish under evaluation at the
                # critical point, while evaluation of 1 remains 1.
                self.assertEqual(obstruction["generator_evaluations"],(0,0,0))
                self.assertEqual(evaluate(f,{(0,0):1},
                                           *obstruction["singular_point"]),1)

    def test_wrong_plus_sign_rejected_in_odd_characteristic(self):
        for name in ("F3","F5","F9","F25","F27"):
            f=FIELDS[name]
            c=f.neg(1)
            receipt=field_oracle(name,1,1,c)
            self.assertNotEqual(receipt["delta"],0)
            self.assertTrue(receipt["unit_if_nonzero"])

    def test_characteristic_two_has_same_criterion(self):
        for name in ("F2","F4","F8","F16"):
            f=FIELDS[name]
            for a,b in ((0,0),(1,0),(0,1),(1,1)):
                c=f.mul(a,b)
                self.assertTrue(singular_ideal_obstruction(f,a,b,c)
                                ["all_generators_zero"])
                good=f.add(c,1)
                self.assertTrue(conic_unit_certificate(f,a,b,good)
                                ["unit_identity"])

    def test_every_singular_parameter_has_unique_critical_point(self):
        for name in ("F2","F3","F4","F5"):
            f=FIELDS[name]
            for a,b in product(range(f.q),repeat=2):
                c=f.mul(a,b)
                root=(f.neg(b),f.neg(a))
                self.assertEqual(singular_ideal_obstruction(f,a,b,c)
                                 ["singular_point"],root)

    def test_discriminant_zero_detected_by_evaluating_generators(self):
        rng=random.Random(261100816)
        for name,f in FIELDS.items():
            for _ in range(50):
                a,b,c=(rng.randrange(f.q) for _ in range(3))
                obstruction=singular_ideal_obstruction(f,a,b,c)
                self.assertEqual(obstruction["all_generators_zero"],
                                 obstruction["delta"]==0)

    def test_ideal_top_is_not_inferred_from_finite_point_sampling(self):
        f=FIELDS["F4"]
        # X^4-X is a nonzero formal polynomial with zero evaluations.
        # The Jacobian iff theorem is about the explicit conic ideal,
        # using a genuine ring homomorphism and a Bézout identity.
        vals=[f.sub(f.pow(x,4),x) for x in range(f.q)]
        self.assertEqual(vals,[0]*f.q)
        for c in (0,1):
            r=field_oracle("F4",1,1,c)
            self.assertEqual(r["unit_if_nonzero"],r["delta"]!=0)


if __name__=="__main__":
    unittest.main()
