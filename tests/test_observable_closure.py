"""NRF-04 independent rational enumeration of robust gate closure and Pareto."""
import unittest
from fractions import Fraction as Q
from itertools import product
from research.compactification.observable_closure import (
    in_span, robust_gate_closure, jordan_frontier,
    jordan_direct_leak_square, optimal_tradeoff_error, tradeoff_cost,
)


class ObservableClosureTests(unittest.TestCase):
    def test_jordan_rank_jump(self):
        w1=((Q(0), Q(1)),)
        w2=((Q(3),), (Q(0),))
        a=robust_gate_closure(((Q(1), Q(0)),),w1,w2)
        self.assertEqual(a["rank_history"],(1,2))
        b=robust_gate_closure(((Q(0), Q(1)),),w1,w2)
        self.assertEqual(b["rank"],1)

    def test_512_binary_weight_scenarios(self):
        cases=0
        for a in product((Q(0),Q(1)),repeat=4):
            w1=(a[:2],a[2:])
            for b in product((Q(0),Q(1)),repeat=4):
                w2=(b[:2],b[2:])
                for teacher in (((Q(1),Q(0)),),((Q(0),Q(1)),)):
                    r=robust_gate_closure(teacher,w1,w2)
                    self.assertLessEqual(r["rank"],2)
                    for v in teacher:
                        self.assertTrue(in_span(v,r["basis"]))
                    for u in r["basis"]:
                        for j in range(2):
                            c=sum((u[i]*w2[i][j] for i in range(2)),Q(0))
                            v=tuple(c*w1[j][i] for i in range(2))
                            self.assertTrue(in_span(v,r["basis"]))
                    self.assertEqual(robust_gate_closure(r["basis"],w1,w2)["rank"],r["rank"])
                    cases+=1
        self.assertEqual(cases,512)

    def test_108_exact_jordan_pareto_matrices(self):
        cases=0
        for t in (Q(-3),Q(-2),Q(-1),Q(-1,2),Q(0),Q(1,2),Q(1),Q(2),Q(3)):
            u1=(1-t*t)/(1+t*t)
            u2=2*t/(1+t*t)
            for b in (Q(-3,2),Q(-1,3),Q(0),Q(2)):
                error,leak_sq=jordan_frontier(u1,u2,b)
                for a in (Q(-2),Q(0),Q(3)):
                    self.assertEqual(jordan_direct_leak_square(u1,u2,a,b),leak_sq)
                    self.assertEqual(leak_sq,b*b*(1-error)**2)
                    cases+=1
        self.assertEqual(cases,108)

    def test_exact_weighted_optimal_frontier(self):
        for b in (Q(-2),Q(-1,4),Q(0),Q(3)):
            for weight in (Q(0),Q(1,16),Q(1),Q(8),Q(30)):
                e=optimal_tradeoff_error(weight,b)
                self.assertGreaterEqual(e,0)
                self.assertLessEqual(e,1)
                cost=tradeoff_cost(e,weight,b)
                for k in range(65):
                    self.assertLessEqual(cost,tradeoff_cost(Q(k,64),weight,b))


if __name__=="__main__":
    unittest.main()
