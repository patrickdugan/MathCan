"""NRF-02 independent exact arithmetic regression tests."""
import unittest
from fractions import Fraction as Q
from itertools import product
from research.compactification.graph_switching import (
    WeightedEdge, bellman_potential, cycle_products, cycles_satisfy,
    count_paths, cover_certificate, explicit_error_sum, guard_locked,
    path_products, scaled_path_bound, weighted_errors,
)

class GraphSwitchingMathTests(unittest.TestCase):
    def test_two_node_cycle_equivalence_grid(self):
        vs=("u","v"); alpha=Q(3,4); count=0
        for a,b,c,d in product((Q(0),Q(1,4),Q(3,4),Q(3,2)),repeat=4):
            es=(WeightedEdge("uu","u","u",a),WeightedEdge("uv","u","v",b),
                WeightedEdge("vu","v","u",c),WeightedEdge("vv","v","v",d))
            criterion=cycles_satisfy(vs,es,alpha)
            self.assertEqual(criterion,a<=alpha and d<=alpha and b*c<=alpha*alpha)
            if criterion:
                w=bellman_potential(vs,es,alpha)
                self.assertTrue(all(e.rate*w[e.src]<=alpha*w[e.dst] for e in es))
            else:
                with self.assertRaises(ValueError): bellman_potential(vs,es,alpha)
            count+=1
        self.assertEqual(count,256)

    def test_three_node_cycle_equivalence_grid(self):
        vs=("u","v","w")
        layouts=(("u","v"),("v","u"),("v","w"),("w","v"),("w","u"),("u","w"))
        alpha=Q(3,4)
        for rates in product((Q(0),Q(1,2),Q(3,2)),repeat=6):
            edges=tuple(WeightedEdge(str(i),u,v,r)
                        for i,((u,v),r) in enumerate(zip(layouts,rates)))
            allowed=cycles_satisfy(vs,edges,alpha)
            try:
                weights=bellman_potential(vs,edges,alpha)
                self.assertTrue(allowed)
                for e in edges:
                    self.assertLessEqual(e.rate*weights[e.src],alpha*weights[e.dst])
            except ValueError:
                self.assertFalse(allowed)

    def test_path_multiplicative_bound_exhaustive(self):
        vs=("a","b","c")
        es=(WeightedEdge("ab","a","b",Q(3,2)),
            WeightedEdge("ba","b","a",Q(1,4)),
            WeightedEdge("bc","b","c",Q(1,2)),
            WeightedEdge("ca","c","a",Q(1,4)),
            WeightedEdge("aa","a","a",Q(1,2)),
            WeightedEdge("cc","c","c",Q(1,2)))
        w=bellman_potential(vs,es,Q(3,4))
        self.assertEqual(w,{"a":Q(1),"b":Q(2),"c":Q(4,3)})
        current=[(v,()) for v in vs]; trials=0
        for depth in range(7):
            succ=[]
            for start,path in current:
                finish,gain=path_products(vs,es,start,path)
                self.assertLessEqual(gain,scaled_path_bound(w,Q(3,4),start,finish,len(path)))
                trials+=1
                succ.extend((start,path+(e.name,)) for e in es if e.src==finish)
            current=succ
        self.assertGreater(trials,100)

    def test_weighted_disturbance_exact(self):
        for rates in product((Q(0),Q(1,2),Q(3,2)),repeat=4):
            for ds in product((Q(0),Q(1,100)),repeat=4):
                self.assertEqual(weighted_errors(rates,ds,Q(1,7)),
                                 explicit_error_sum(rates,ds,Q(1,7)))

    def test_guard_hyperplane_strict_equality(self):
        self.assertTrue(guard_locked(Q(3,4),Q(1),Q(1,2)))
        self.assertFalse(guard_locked(Q(1,2),Q(1),Q(1,2)))
        self.assertFalse(guard_locked(Q(1,4),Q(1),Q(1,2)))

    def test_cover_count_and_diameter(self):
        vs=("a","b")
        es=(WeightedEdge("aa","a","a",Q(1,2)),
            WeightedEdge("ab","a","b",Q(1,2)),
            WeightedEdge("ba","b","a",Q(1,2)),
            WeightedEdge("bb","b","b",Q(1,2)))
        w=bellman_potential(vs,es,Q(3,4))
        for depth in range(9):
            paths,diam=cover_certificate(vs,es,w,Q(3,4),depth,Q(2))
            self.assertEqual(paths,2*(2**depth))
            self.assertEqual(diam,2*Q(3,4)**depth)
        self.assertEqual(count_paths(vs,es,0),2)

if __name__=="__main__":
    unittest.main()
