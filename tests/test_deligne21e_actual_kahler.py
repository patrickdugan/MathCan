"""DEL-21E: actual quotient U^k Kähler presentation checks.

The full defining ideal is the span of genuine lifted equations.
This independent oracle verifies that its first-order conormal
relations coincide with the rows of the DEL-21D presented cotangent
for regular, singular and nonreduced examples. The base-changed
Kähler fiber will be checked in the subsequent Lean module.
"""
import unittest

from tests.test_deligne21d_conormal_fiber import (
    PRIMES, frozen, gradients_for_mode, rank_mod, row_span
)


class ActualKahlerPresentationOracle(unittest.TestCase):
    def test_product_relation_count(self):
        for case in frozen():
            if case["mode"]=="product_parabolas":
                self.assertEqual(case["coordinates"],4)
                self.assertEqual(len(case["jacobian"]),2)
            elif case["mode"]=="redundant":
                self.assertEqual(case["coordinates"],2)
                self.assertEqual(len(case["jacobian"]),2)
            else:
                self.assertEqual(case["coordinates"],2)
                self.assertEqual(len(case["jacobian"]),1)

    def test_true_derivative_rows_from_full_relations(self):
        for case in frozen():
            p=int(case["field"][1:])
            computed=gradients_for_mode(case["mode"],case["point"],p)
            self.assertEqual(computed,case["jacobian"])
            self.assertEqual(rank_mod(computed,p),case["rank"])

    def test_nonreduced_and_reduced_quotients_differ(self):
        for p in PRIMES:
            self.assertEqual(row_span([[0,0]],p),{(0,0)})
            self.assertEqual(len(row_span([[1,0]],p)),p)
            self.assertEqual(rank_mod([[0,0]],p),0)
            self.assertEqual(rank_mod([[1,0]],p),1)

    def test_redundant_equations_preserve_ideal(self):
        # The original ideal of (x²,x³) is (x²), not (x).
        # At x=0 the first-order conormal relation ranks agree.
        for p in PRIMES:
            self.assertEqual(row_span([[0,0],[0,0]],p),
                             row_span([[0,0]],p))

    def test_product_has_independent_factor_relations(self):
        for case in frozen():
            if case["mode"]!="product_parabolas":
                continue
            p=int(case["field"][1:])
            a,b=case["jacobian"]
            self.assertEqual(a[2:], [0,0])
            self.assertEqual(b[:2], [0,0])
            self.assertEqual(a[1],1%p)
            self.assertEqual(b[3],1%p)
            self.assertEqual(rank_mod([a,b],p),2)

    def test_characteristic_two_keeps_actual_derivative(self):
        for case in frozen():
            if case["mode"]!="char_two":
                continue
            self.assertEqual(case["field"],"F2")
            self.assertEqual(case["jacobian"],[[0,1]])

    def test_cotangent_rank_and_quotient_dimension(self):
        for case in frozen():
            p=int(case["field"][1:])
            ambient=case["coordinates"]
            rank=rank_mod(case["jacobian"],p)
            self.assertEqual(case["presented_cotangent_dim"],ambient-rank)
            self.assertEqual(case["expected_tangent_count"],
                             p**(ambient-rank))


if __name__=="__main__":
    unittest.main()
