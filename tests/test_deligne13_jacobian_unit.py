"""DEL-13 exact global Jacobian ideal and Bézout certificate regressions."""
from itertools import product
import random
import unittest

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del12_oracle import evaluate
from research.deligne_sign_audit.del13_oracle import (
    poly_add, poly_neg, poly_sub, poly_mul, poly_scalar, constant,
    conic_bezout, conic_unit_certificate,
    singular_ideal_obstruction, wrong_sign_certificate,
    swapped_factor_certificate, field_oracle,
)
from research.deligne_sign_audit.del13_verify_tasks import verify


class Deligne13GlobalJacobianTests(unittest.TestCase):
    def test_all_96_exact_receipts(self):
        self.assertEqual(sum(verify().values()),96)

    def test_bezout_polynomial_identity_all_small_fields(self):
        for name in ("F2","F3","F4","F5"):
            f=FIELDS[name]
            for a,b,c in product(range(f.q),repeat=3):
                with self.subTest(field=name,a=a,b=b,c=c):
                    receipt=conic_bezout(f,a,b,c)
                    self.assertTrue(receipt["identity"])
                    self.assertEqual(receipt["lhs"],constant(f,receipt["delta"]))

    def test_true_unit_ideal_certificates(self):
        rng=random.Random(261100813)
        for name,f in FIELDS.items():
            for _ in range(90):
                a,b,c=(rng.randrange(f.q) for _ in range(3))
                receipt=conic_bezout(f,a,b,c)
                cert=conic_unit_certificate(f,a,b,c)
                if receipt["delta"]==0:
                    self.assertIsNone(cert)
                    continue
                self.assertIsNotNone(cert)
                self.assertTrue(cert["unit_identity"])
                witness=poly_add(f,
                    poly_mul(f,cert["coeffs"]["F"],receipt["F"]),
                    poly_mul(f,cert["coeffs"]["dx"],receipt["dx"]))
                self.assertEqual(witness,constant(f,1))
                self.assertEqual(f.mul(cert["inverse"],receipt["delta"]),1)

    def test_singular_evaluation_obstructs_unit_ideal(self):
        rng=random.Random(261100814)
        for name,f in FIELDS.items():
            for _ in range(75):
                a,b=(rng.randrange(f.q) for _ in range(2))
                c=f.mul(a,b)
                obstruction=singular_ideal_obstruction(f,a,b,c)
                self.assertTrue(obstruction["all_generators_zero"])
                self.assertEqual(obstruction["generator_evaluations"],(0,0,0))
                self.assertIsNone(conic_unit_certificate(f,a,b,c))
                self.assertFalse(obstruction["certificate_exists"])

    def test_jacobian_unit_iff_discriminant_nonzero_finite_shadow(self):
        for name,f in FIELDS.items():
            for _ in range(60):
                a,b,c=(_+1)%f.q,(_*2+1)%f.q,(_*3+2)%f.q
                result=field_oracle(name,a,b,c)
                self.assertEqual(result["unit_if_nonzero"],result["delta"]!=0)
                self.assertEqual(result["singular_if_zero"],result["delta"]==0)
                self.assertTrue(result["identity"])

    def test_reject_wrong_discriminant_sign(self):
        for name in ("F3","F5","F9","F25","F27"):
            f=FIELDS[name]
            a,b,c=1,1,f.neg(1)
            self.assertEqual(wrong_sign_certificate(f,a,b,c),0)
            self.assertNotEqual(conic_bezout(f,a,b,c)["delta"],0)

    def test_reject_wrong_derivative_factor(self):
        for name,f in FIELDS.items():
            for a,b,c in ((1,0,1),(0,1,1),(1,1,0)):
                self.assertFalse(swapped_factor_certificate(f,a,b,c))

    def test_characteristic_two_unit_witness(self):
        for name in ("F2","F4","F8","F16"):
            f=FIELDS[name]
            for a,b in ((0,0),(1,0),(0,1),(1,1)):
                c=f.add(f.mul(a,b),1)
                cert=conic_unit_certificate(f,a,b,c)
                self.assertIsNotNone(cert)
                self.assertTrue(cert["unit_identity"])
                self.assertEqual(cert["inverse"],1)

    def test_constant_and_zero_polynomial_arithmetic(self):
        for name,f in FIELDS.items():
            self.assertEqual(poly_add(f,{},{}),{})
            self.assertEqual(poly_mul(f,{},constant(f,1)),{})
            self.assertEqual(poly_sub(f,constant(f,1),constant(f,1)),{})
            self.assertEqual(poly_scalar(f,0,constant(f,1)),{})
            self.assertEqual(poly_mul(f,constant(f,1),constant(f,1)),constant(f,1))

    def test_bezout_polynomial_identity_at_points(self):
        rng=random.Random(261100815)
        for name,f in FIELDS.items():
            for _ in range(75):
                a,b,c,x,y=(rng.randrange(f.q) for _ in range(5))
                receipt=conic_bezout(f,a,b,c)
                lhs=evaluate(f,receipt["F"],x,y)
                subterm=f.mul(evaluate(f,receipt["dy"],x,y),
                              evaluate(f,receipt["dx"],x,y))
                self.assertEqual(f.sub(lhs,subterm),receipt["delta"])

    def test_ideal_on_discriminant_has_a_geometric_obstruction(self):
        for name,f in FIELDS.items():
            for a in range(min(f.q,4)):
                for b in range(min(f.q,4)):
                    c=f.mul(a,b)
                    obs=singular_ideal_obstruction(f,a,b,c)
                    self.assertTrue(obs["all_generators_zero"])
                    self.assertEqual(obs["singular_point"],(f.neg(b),f.neg(a)))

    def test_nonzero_discriminant_certificate_for_all_conics_F2(self):
        f=FIELDS["F2"]
        results=[]
        for a,b,c in product(range(2),repeat=3):
            cert=conic_unit_certificate(f,a,b,c)
            results.append(cert is not None)
        self.assertEqual(sum(results),4)


if __name__=="__main__":
    unittest.main()
