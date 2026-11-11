from fractions import Fraction as F
from itertools import product
import random
import unittest
from research.toe.graph_entropy import Graph,action,coarse_action,gradients,rational_detailed_balance,kernel
from research.toe.frw_null import frw_obstruction,frw_null_relations,frw_signal


class GraphEntropyTests(unittest.TestCase):
    def setUp(self):
        self.cycle=Graph(3,((0,1),(1,2),(2,0)))

    def test_triangle_gauge_obstruction(self):
        self.assertEqual(action(self.cycle,[0,0,1],[1,1,1]),F(1,6))
        for p in product((-1,0,1),repeat=3):
            base=gradients(self.cycle,p)
            self.assertEqual(action(self.cycle,base,[1,2,3]),0)

    def test_cycle_is_sufficient_and_tree_loses_it(self):
        for quotes in product((-1,0,1),repeat=3):
            full=action(self.cycle,quotes,[1,2,3])
            self.assertEqual(full,coarse_action(self.cycle,quotes,[1,2,3],[[1,1,1]]))
        self.assertEqual(coarse_action(self.cycle,[0,0,1],[1,1,1],
                                       [[1,0,0],[0,1,0]]),0)

    def test_gauge_invariance(self):
        for obs in product((-1,0,1),repeat=3):
            full=action(self.cycle,obs,[1,2,3])
            for p in ((5,7,3),(0,1,1),(-2,-4,3)):
                self.assertEqual(full,action(self.cycle,
                                 [a+b for a,b in zip(obs,gradients(self.cycle,p))],[1,2,3]))

    def test_coarse_information_monotonicity(self):
        rnd=random.Random(24111)
        for _ in range(180):
            x=[rnd.randint(-4,4) for _ in range(3)]
            sig=[rnd.randint(1,5) for _ in range(3)]
            a=[[rnd.randint(-2,2) for _ in range(3)] for _ in range(2)]
            if kernel(a,3) and len(kernel(a,3))==1:
                if kernel(list(map(list,zip(*a))),2):continue
                self.assertLessEqual(coarse_action(self.cycle,x,sig,a),action(self.cycle,x,sig))

    def test_detailed_balance(self):
        self.assertIsNone(rational_detailed_balance(self.cycle,[2,2,2],[1,1,1]))
        self.assertIsNotNone(rational_detailed_balance(self.cycle,[2,3,1],[1,1,6]))

    def test_parallel_edge_and_tree(self):
        self.assertEqual(action(Graph(2,((0,1),(0,1))),[0,1],[1,1]),F(1,4))
        self.assertEqual(action(Graph(4,((0,1),(1,2),(2,3))),[4,-2,5],[1,2,3]),0)

    def test_bad_channel(self):
        with self.assertRaises(ValueError):
            coarse_action(self.cycle,[1,2,3],[1,1,1],[[1,0,0],[1,0,0]])


class FRWTests(unittest.TestCase):
    def test_dimension(self):
        self.assertEqual(len(frw_null_relations([0,1,2,3])),0)
        self.assertEqual(len(frw_null_relations([0,1,2,3,4])),1)
        self.assertEqual(len(frw_null_relations([0,1,2,3,4,5,6])),3)

    def test_null_fits(self):
        z=[0,1,2,3,4,5]
        for p in ((1,0,2,1),(0,F(1,10),F(1,3),F(1,20)),(4,-1,3,1)):
            self.assertEqual(frw_obstruction(z,frw_signal(z,p),[1]*6),0)

    def test_dynamic_linear_dark_energy(self):
        z=[0,1,2,3,4]
        base=frw_signal(z,(1,0,3,1))
        perturb=[F(1+i) for i in z]
        self.assertEqual(frw_obstruction(z,[a+b for a,b in zip(base,perturb)],[1]*5),
                         F(36,60995))

    def test_physical_nuisance_degeneracy(self):
        z=[0,1,2,3,4]
        for d in (0,2,3,4):
            self.assertEqual(frw_obstruction(z,[(1+i)**d for i in z],[1]*5),0)


if __name__=="__main__":unittest.main()
