"""DEL-10 exact finite-field tests of Nullstellensatz nonvanishing gates."""
import random
import unittest

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del10_oracle import (
    canonical_polynomial, degree_vector, evaluate, exact_case,
    find_common_witness, degree_budget, linear_term, constant,
    frobenius_gap_terms, high_degree_nonzero_terms,
)
from research.deligne_sign_audit.del10_verify_tasks import verify


class Deligne10FiniteOpenTests(unittest.TestCase):
    def test_all_81_labeled_cases(self):
        self.assertEqual(sum(verify().values()),81)

    def test_every_nonzero_univariate_degree_below_three_has_point(self):
        f=FIELDS["F3"]
        for a in range(f.q):
            for b in range(f.q):
                for c in range(f.q):
                    if a==b==c==0:
                        continue
                    P=canonical_polynomial(f,[(a,[0]),(b,[1]),(c,[2])],1)
                    self.assertTrue(P)
                    self.assertLess(degree_vector(P,1)[0],f.q)
                    self.assertIsNotNone(find_common_witness(f,[P],1))

    def test_all_nonzero_multiaffine_polynomials_over_F2_have_point(self):
        f=FIELDS["F2"]
        for mask in range(1,16):
            terms=[]
            for j,(e0,e1) in enumerate(((0,0),(1,0),(0,1),(1,1))):
                if mask&(1<<j):
                    terms.append((1,[e0,e1]))
            P=canonical_polynomial(f,terms,2)
            self.assertTrue(P)
            self.assertTrue(all(d<f.q for d in degree_vector(P,2)))
            self.assertIsNotNone(find_common_witness(f,[P],2))

    def test_three_open_loci_have_common_witness_if_degree_budget_fits(self):
        rng=random.Random(261100802)
        for name in ("F3","F4","F5","F8","F9","F16","F25","F27"):
            f=FIELDS[name]
            for _ in range(15):
                a,b=rng.sample(range(f.q),2)
                terms=[
                    linear_term(f,a,0,2),
                    linear_term(f,b,0,2),
                    linear_term(f,0,1,2)]
                receipt=exact_case(name,terms,2)
                self.assertTrue(receipt["strict_degree_gate"])
                self.assertTrue(receipt["exists"])
                self.assertEqual(receipt["degrees"],(2,1))

    def test_F2_independent_coordinate_constraints(self):
        f=FIELDS["F2"]
        receipt=exact_case("F2",[
            linear_term(f,0,0,2),linear_term(f,0,1,2),
            constant(f,1,2)],2)
        self.assertTrue(receipt["strict_degree_gate"])
        self.assertEqual(receipt["witness"],(1,1))

    def test_F2_incompatible_opens_require_extension(self):
        f=FIELDS["F2"]
        receipt=exact_case("F2",[
            linear_term(f,0,0,1),linear_term(f,1,0,1)],1)
        self.assertFalse(receipt["strict_degree_gate"])
        self.assertFalse(receipt["exists"])
        F=FIELDS["F4"]
        repaired=exact_case("F4",[
            linear_term(F,0,0,1),linear_term(F,1,0,1)],1)
        self.assertTrue(repaired["strict_degree_gate"])
        self.assertTrue(repaired["exists"])

    def test_frobenius_gap_mutants(self):
        for base,ext in (("F2","F4"),("F3","F9"),("F5","F25")):
            f=FIELDS[base]
            bad=exact_case(base,[frobenius_gap_terms(f)],1)
            self.assertTrue(bad["nonzero_polynomials"])
            self.assertFalse(bad["strict_degree_gate"])
            self.assertFalse(bad["exists"])
            extf=FIELDS[ext]
            repaired=exact_case(ext,[frobenius_gap_terms(extf)],1)
            self.assertTrue(repaired["strict_degree_gate"])
            self.assertTrue(repaired["exists"])

    def test_high_degree_condition_is_sufficient(self):
        for name,f in FIELDS.items():
            receipt=exact_case(name,[high_degree_nonzero_terms(f)],1)
            self.assertFalse(receipt["strict_degree_gate"])
            self.assertTrue(receipt["exists"])
            self.assertEqual(evaluate(f,receipt["polynomials"][0],(0,)),1)

    def test_zero_polynomial_is_not_eligible(self):
        for name,f in FIELDS.items():
            receipt=exact_case(name,[[(0,[0])]],1)
            self.assertFalse(receipt["nonzero_polynomials"])
            self.assertTrue(receipt["strict_degree_gate"])
            self.assertFalse(receipt["exists"])

    def test_constant_nonzero_good_open(self):
        for name,f in FIELDS.items():
            receipt=exact_case(name,[constant(f,1,3)],3)
            self.assertTrue(receipt["strict_degree_gate"])
            self.assertEqual(receipt["witness"],(0,0,0))

    def test_formal_polynomial_not_confused_with_polynomial_function(self):
        f=FIELDS["F4"]
        P=canonical_polynomial(f,[(1,[4]),(f.neg(1),[1])],1)
        self.assertTrue(P)
        self.assertTrue(all(evaluate(f,P,(x,))==0 for x in range(f.q)))
        self.assertEqual(degree_vector(P,1),(4,))

    def test_reject_negative_exponents_and_outside_field_coefficients(self):
        for name,f in FIELDS.items():
            with self.assertRaisesRegex(ValueError,"multidegree"):
                canonical_polynomial(f,[(1,[-1])],1)
            with self.assertRaisesRegex(ValueError,"outside"):
                canonical_polynomial(f,[(f.q,[0])],1)


if __name__=="__main__":
    unittest.main()
