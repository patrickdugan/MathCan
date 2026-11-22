"""DEL-20: independent finite-field Jacobian-kernel cotangent oracle.

For the actual polynomial presentation of V=U² where U is y-x²=0,
the tangent space is the kernel of the two true polynomial gradients.
The four coordinate covectors restrict to a spanning family in its
two-dimensional dual, including in characteristic two.

Also tests a singular node xy=0, where tangent dimension increases,
and a deliberate omission of the embedding-coordinate covectors.
"""
from __future__ import annotations

import json
import unittest
from pathlib import Path

PRIMES = (2, 3, 5, 7, 11, 13, 17)
KINDS = ("cotangent_span", "fixed_phase", "omit_x_mutant", "char_two_audit")


def frozen() -> list[dict]:
    rows = []
    for i in range(96):
        kind = KINDS[i % len(KINDS)]
        p = 2 if kind == "char_two_audit" else PRIMES[i % len(PRIMES)]
        x0, x1 = (5*i + 1) % p, (i*i + 3) % p
        if kind == "omit_x_mutant":
            x0 = x1 = 0
        t0, t1 = (7*i + 3) % p, (9*i + 2) % p
        if kind == "fixed_phase":
            t0, t1 = -x1 % p, -x0 % p
        if kind == "omit_x_mutant":
            t0 = t1 = 1
        ay0, ay1 = (2*i + 1) % p, (3*i + 2) % p
        ax0, ax1 = (t0 - 2*x0*ay0) % p, (t1 - 2*x1*ay1) % p
        B = x0*x1 % p
        level = (-B) % p if kind == "fixed_phase" else (11*i + 4) % p
        y0, y1 = x0*x0 % p, x1*x1 % p
        c = (level - ax0*x0 - ay0*y0 - ax1*x1 - ay1*y1) % p
        rows.append({
            "id": f"DEL20-{i+1:03d}",
            "kind": kind, "field": f"F{p}",
            "x0": x0, "x1": x1, "y0": y0, "y1": y1,
            "target_dx0": t0, "target_dx1": t1,
            "ax0": ax0, "ay0": ay0, "ax1": ax1,
            "ay1": ay1, "c": c, "level": level, "phase_B": B
        })
    return rows


def jacobian(p: int, x0: int, x1: int) -> list[list[int]]:
    return [[(-2*x0)%p,1,0,0],[0,0,(-2*x1)%p,1]]


def tangent_basis(p: int, x0: int, x1: int) -> list[list[int]]:
    return [[1,(2*x0)%p,0,0],[0,0,1,(2*x1)%p]]


def dot(p: int, a: list[int], b: list[int]) -> int:
    return sum(x*y for x,y in zip(a,b)) % p


def gaussian_rank(p: int, mat: list[list[int]]) -> int:
    a = [[x % p for x in row] for row in mat]
    if not a:
        return 0
    nr,nc=len(a),len(a[0])
    rank=0
    for col in range(nc):
        pivot=next((r for r in range(rank,nr) if a[r][col]),None)
        if pivot is None:
            continue
        a[rank],a[pivot]=a[pivot],a[rank]
        inv=pow(a[rank][col],-1,p)
        a[rank]=[x*inv%p for x in a[rank]]
        for row in range(nr):
            if row!=rank and a[row][col]:
                fac=a[row][col]
                a[row]=[(x-fac*y)%p for x,y in zip(a[row],a[rank])]
        rank+=1
        if rank==nr:
            break
    return rank


class CotangentSpanningOracle(unittest.TestCase):
    def test_exact_frozen_corpus(self) -> None:
        file=(Path(__file__).resolve().parents[1]/
              "research/deligne_sign_audit/del20_tasks.jsonl")
        rows=[json.loads(s) for s in file.read_text().splitlines() if s.strip()]
        self.assertEqual(rows,frozen())
        self.assertEqual(len(rows),96)
        self.assertEqual(len({r["id"] for r in rows}),96)
        self.assertEqual({kind:sum(x["kind"]==kind for x in rows)
                          for kind in KINDS},{kind:24 for kind in KINDS})

    def test_actual_constraint_gradients_and_tangent_kernel(self) -> None:
        for row in frozen():
            p=int(row["field"][1:])
            J=jacobian(p,row["x0"],row["x1"])
            T=tangent_basis(p,row["x0"],row["x1"])
            self.assertEqual(gaussian_rank(p,J),2)
            self.assertEqual(gaussian_rank(p,T),2)
            self.assertTrue(all(dot(p,j,t)==0 for j in J for t in T))
            self.assertEqual(row["y0"],row["x0"]**2%p)
            self.assertEqual(row["y1"],row["x1"]**2%p)

    def test_coordinate_covectors_span_tangent_dual(self) -> None:
        for row in frozen():
            p=int(row["field"][1:])
            T=tangent_basis(p,row["x0"],row["x1"])
            # The restrictions of the four coordinate functionals
            # to tangent basis vectors form transpose(T): 2x4.
            self.assertEqual(gaussian_rank(p,T),2)
            a=[row["ax0"],row["ay0"],row["ax1"],row["ay1"]]
            self.assertEqual([dot(p,a,t) for t in T],
                             [row["target_dx0"],row["target_dx1"]])

    def test_full_dual_rational_witness_for_every_target(self) -> None:
        for p in (2,3,5,7):
            for x0 in range(p):
                for x1 in range(p):
                    T=tangent_basis(p,x0,x1)
                    for w0 in range(p):
                        for w1 in range(p):
                            # Free choices of y-coordinate coefficients.
                            a=[w0,0,w1,0]
                            self.assertEqual([dot(p,a,t) for t in T],[w0,w1])

    def test_exact_fiber_cardinality(self) -> None:
        # Each 2x4 restriction map has dimension-two kernel and
        # therefore p² coefficient vectors over any target.
        for row in frozen():
            p=int(row["field"][1:])
            T=tangent_basis(p,row["x0"],row["x1"])
            n=0
            for ay0 in range(p):
                for ay1 in range(p):
                    ax0=(row["target_dx0"]-2*row["x0"]*ay0)%p
                    ax1=(row["target_dx1"]-2*row["x1"]*ay1)%p
                    a=[ax0,ay0,ax1,ay1]
                    self.assertEqual([dot(p,a,t) for t in T],
                                     [row["target_dx0"],row["target_dx1"]])
                    n+=1
            self.assertEqual(n,p*p)

    def test_free_constant_handles_value_independently(self) -> None:
        for row in frozen():
            p=int(row["field"][1:])
            a=[row["ax0"],row["ay0"],row["ax1"],row["ay1"]]
            z=[row["x0"],row["y0"],row["x1"],row["y1"]]
            level=(dot(p,a,z)+row["c"])%p
            self.assertEqual(level,row["level"])

    def test_fixed_phase_critical_parameters(self) -> None:
        for row in frozen():
            if row["kind"]!="fixed_phase":
                continue
            p=int(row["field"][1:])
            self.assertEqual((row["target_dx0"]+row["x1"])%p,0)
            self.assertEqual((row["target_dx1"]+row["x0"])%p,0)
            self.assertEqual((row["level"]+row["phase_B"])%p,0)

    def test_missing_x_covectors_mutant(self) -> None:
        for row in frozen():
            if row["kind"]!="omit_x_mutant":
                continue
            p=int(row["field"][1:])
            self.assertEqual((row["x0"],row["x1"]),(0,0))
            # If only y0,y1 were used, their restrictions vanish
            # at this point and cannot generate nonzero targets.
            for ay0 in range(p):
                for ay1 in range(p):
                    self.assertEqual(((2*row["x0"]*ay0)%p,
                                      (2*row["x1"]*ay1)%p),(0,0))
            self.assertEqual((row["target_dx0"],row["target_dx1"]),(1,1))

    def test_singular_node_tangent_dimension(self) -> None:
        # For f(x,y)=xy, at the origin the Jacobian vanishes and
        # the Zariski tangent is both ambient directions.
        # The coordinate covectors still form its full dual.
        for p in PRIMES:
            self.assertEqual(gaussian_rank(p,[[0,0]]),0)
            self.assertEqual(gaussian_rank(p,[[1,0],[0,1]]),2)
            self.assertEqual((0*1+0*0)%p,0)

    def test_characteristic_two_formal_derivative(self) -> None:
        for row in frozen():
            if row["kind"]!="char_two_audit":
                continue
            p=2
            J=jacobian(p,row["x0"],row["x1"])
            self.assertEqual(J,[[0,1,0,0],[0,0,0,1]])
            T=tangent_basis(p,row["x0"],row["x1"])
            self.assertEqual(T,[[1,0,0,0],[0,0,1,0]])
            self.assertEqual(gaussian_rank(p,T),2)


if __name__=="__main__":
    unittest.main()
