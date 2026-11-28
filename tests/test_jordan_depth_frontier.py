"""NRF-07: finite exact-rational checks of nilpotent depth/Pareto formula."""
import unittest
from fractions import Fraction as Q
from itertools import product
from research.compactification.jordan_depth_frontier import (
    jordan_power, repeated_product, rational_circle,
    rank_one_error_and_leakage, direct_leakage_sq,
    crossover_lambda, objective, optimum_risk,
)


class JordanDepthFrontierTests(unittest.TestCase):
    def test_closed_form_vs_independent_matrix_multiplication(self):
        count = 0
        for a,b,n in product(
            (Q(-2),Q(-1),Q(-1,2),Q(0),Q(1,2),Q(1),Q(2)),
            (Q(-3),Q(0),Q(2,5)),
            range(13),
        ):
            self.assertEqual(jordan_power(a,b,n),repeated_product(a,b,n))
            count += 1
        self.assertEqual(count, 273)

    def test_exact_projector_leakage(self):
        count=0
        for a,b,n,t in product(
            (Q(-2),Q(-1),Q(0),Q(1,2),Q(1)),
            (Q(-3),Q(0),Q(2,5)),
            range(1,10),
            (Q(-2),Q(-1,2),Q(0),Q(1,2),Q(1),Q(2)),
        ):
            u=rational_circle(t)
            E,L=rank_one_error_and_leakage(a,b,n,u)
            self.assertEqual(L*L,direct_leakage_sq(a,b,n,u))
            self.assertEqual(E,u[1]**2)
            count+=1
        self.assertEqual(count, 810)

    def test_pairwise_threshold_and_depth_fourfold(self):
        risks=(Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1))
        count=0
        for i in range(len(risks)):
            for j in range(i+1,len(risks)):
                e1,e2=risks[i],risks[j]
                for b in (Q(-3,2),Q(1,3),Q(2)):
                    l=crossover_lambda(1,b,4,e1,e2)
                    self.assertEqual(objective(1,b,4,e1,l),
                                     objective(1,b,4,e2,l))
                    self.assertEqual(crossover_lambda(1,b,8,e1,e2),l/4)
                    self.assertLess(objective(1,b,4,e1,l/2),
                                    objective(1,b,4,e2,l/2))
                    self.assertGreater(objective(1,b,4,e1,l*2),
                                       objective(1,b,4,e2,l*2))
                    count+=1
        self.assertEqual(count, 30)

    def test_optimal_risk_on_rational_grid(self):
        for a in (Q(1),Q(1,2)):
            for b in (Q(1,4),Q(1),Q(2)):
                for n in (1,2,4,8):
                    for lam in (Q(0),Q(1,4),Q(1),Q(2),Q(30)):
                        best=optimum_risk(a,b,n,lam)
                        val=objective(a,b,n,best,lam)
                        for k in range(101):
                            self.assertLessEqual(
                                val,objective(a,b,n,Q(k,100),lam))

    def test_zero_shear_or_nilpotent_zero_depth(self):
        self.assertIsNone(crossover_lambda(1,0,3,0,Q(1,2)))
        self.assertIsNone(crossover_lambda(0,1,3,0,Q(1,2)))
        with self.assertRaises(ValueError):
            crossover_lambda(1,1,4,Q(3,4),Q(1,4))


if __name__ == "__main__":
    unittest.main()
