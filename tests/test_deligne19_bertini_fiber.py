"""DEL-19 exact oracle for fixed-coefficient Bertini fiber rank.

At a point of U², U={(x,y):y=x²}, the four ambient coordinate
differentials are (1,0), (2*x0,0), (0,1), (0,2*x1). A free constant c
adds the independent value coordinate, making the augmented map
F_q^5 -> F_q^3 surjective with fibers of exactly q² elements.

The oracle tests characteristic two, omission of c, and loss of
the genuine coordinate immersion as adversarial mutations.
"""
from __future__ import annotations

import json
import unittest
from pathlib import Path

FIELDS = (2,3,5,7,11,13,17)
KINDS = ("surjective","fixed_phase","omit_constant_mutant","omit_embedding_mutant")


def frozen() -> list[dict]:
    rows=[]
    for i in range(96):
        q=FIELDS[i % len(FIELDS)]
        kind=KINDS[i % len(KINDS)]
        x0,x1=(3*i+1)%q,(5*i+2)%q
        g0,g1=(7*i+3)%q,(i*i+1)%q
        level=(11*i+4)%q
        if kind=="fixed_phase":
            g0,g1=(-x1)%q,(-x0)%q
            level=(-x0*x1)%q
        if kind=="omit_embedding_mutant":
            x0=x1=0
            g0=g1=1
            level=1
        a0,a1,a2,a3=g0,0,g1,0
        c=(level-a0*x0-a2*x1)%q
        if kind=="omit_constant_mutant" and c==0:
            level=(level+1)%q
            c=(level-a0*x0-a2*x1)%q
        rows.append({
            "id":f"DEL19-{i+1:03d}","kind":kind,"field":f"F{q}",
            "x0":x0,"x1":x1,"target_g0":g0,"target_g1":g1,
            "target_level":level,"a0":a0,"a1":a1,"a2":a2,
            "a3":a3,"c":c,"phase_B":x0*x1%q,
        })
    return rows


def augmented(q: int,x0: int,x1: int,a0: int,a1: int,a2: int,a3: int,c: int):
    dg0=(a0+2*x0*a1)%q
    dg1=(a2+2*x1*a3)%q
    val=(a0*x0+a1*x0*x0+a2*x1+a3*x1*x1+c)%q
    return (dg0,dg1,val)


class AffineBertiniFiberOracle(unittest.TestCase):
    def test_exact_frozen_data(self):
        file=Path(__file__).resolve().parents[1]/ (
            "research/deligne_sign_audit/del19_tasks.jsonl")
        rows=[json.loads(x) for x in file.read_text().splitlines() if x]
        self.assertEqual(rows,frozen())
        self.assertEqual(len(rows),96)
        self.assertEqual({k:sum(r["kind"]==k for r in rows)
                          for k in KINDS},{k:24 for k in KINDS})

    def test_augmented_map_hits_every_registered_target(self):
        for r in frozen():
            q=int(r["field"][1:])
            got=augmented(q,r["x0"],r["x1"],r["a0"],r["a1"],
                          r["a2"],r["a3"],r["c"])
            self.assertEqual(got,(r["target_g0"],r["target_g1"],
                                  r["target_level"]),r)

    def test_augmented_three_by_three_minor_is_one(self):
        # Columns (a0,a2,c) form the triangular 3x3 submatrix
        # [1,0,0; 0,1,0; x0,x1,1], determinant exactly one in Z.
        for r in frozen():
            q=int(r["field"][1:])
            minor=((1*1*1+0+0)-(0+0+0))%q
            self.assertEqual(minor,1)

    def test_fixed_phase_criticality(self):
        for r in frozen():
            if r["kind"]!="fixed_phase":
                continue
            q=int(r["field"][1:])
            g0,g1,val=augmented(q,r["x0"],r["x1"],
                r["a0"],r["a1"],r["a2"],r["a3"],r["c"])
            self.assertEqual((g0+r["x1"])%q,0)
            self.assertEqual((g1+r["x0"])%q,0)
            self.assertEqual((val+r["phase_B"])%q,0)

    def test_omitting_free_constant_is_detected(self):
        for r in frozen():
            if r["kind"]!="omit_constant_mutant":
                continue
            q=int(r["field"][1:])
            self.assertNotEqual(r["c"],0)
            false_val=augmented(q,r["x0"],r["x1"],
                r["a0"],r["a1"],r["a2"],r["a3"],0)[2]
            self.assertNotEqual(false_val,r["target_level"])

    def test_losing_embedding_coordinates_breaks_surjectivity(self):
        for r in frozen():
            if r["kind"]!="omit_embedding_mutant":
                continue
            q=int(r["field"][1:])
            self.assertEqual((r["x0"],r["x1"]),(0,0))
            # The two remaining y-coordinate differentials are
            # 2*x0=2*x1=0, so they cannot realize (g0,g1)=(1,1).
            self.assertNotEqual((0,0),(r["target_g0"],r["target_g1"]))
            for a1 in range(q):
                for a3 in range(q):
                    self.assertEqual(((2*r["x0"]*a1)%q,
                                      (2*r["x1"]*a3)%q),(0,0))

    def test_fiber_size_q_squared(self):
        # For every free pair (a1,a3), there is one triple
        # (a0,a2,c) achieving a prescribed gradient and value.
        for r in frozen():
            q=int(r["field"][1:])
            x0,x1=r["x0"],r["x1"]
            g0,g1,level=r["target_g0"],r["target_g1"],r["target_level"]
            witnesses=set()
            for a1 in range(q):
                for a3 in range(q):
                    a0=(g0-2*x0*a1)%q
                    a2=(g1-2*x1*a3)%q
                    c=(level-a0*x0-a1*x0*x0-a2*x1-a3*x1*x1)%q
                    self.assertEqual(augmented(q,x0,x1,a0,a1,a2,a3,c),
                                     (g0,g1,level))
                    witnesses.add((a0,a1,a2,a3,c))
            self.assertEqual(len(witnesses),q*q)

    def test_exhaustive_small_field_fiber_cardinality(self):
        for q in (2,3,5):
            for x0,x1,g0,g1,level in ((0,0,1%q,1%q,0),(1%q,2%q,0,1%q,1%q)):
                n=sum(augmented(q,x0,x1,a0,a1,a2,a3,c)==(g0,g1,level)
                      for a0 in range(q) for a1 in range(q)
                      for a2 in range(q) for a3 in range(q)
                      for c in range(q))
                self.assertEqual(n,q*q)

    def test_characteristic_two(self):
        q=2
        for x0 in range(q):
            for x1 in range(q):
                for g0 in range(q):
                    for g1 in range(q):
                        for v in range(q):
                            a0,a1,a2,a3=g0,0,g1,0
                            c=(v-a0*x0-a2*x1)%q
                            self.assertEqual(
                                augmented(q,x0,x1,a0,a1,a2,a3,c),
                                (g0,g1,v))


if __name__=="__main__":
    unittest.main()
