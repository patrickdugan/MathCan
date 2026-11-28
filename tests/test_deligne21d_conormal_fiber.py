"""DEL-21D: actual polynomial Jacobian conormal quotient and tangent dual.

At a rational point of an affine presented scheme, the conormal
rows are the evaluated genuine formal partials of the defining
equations. The presented cotangent space is K^n / rowSpan(J).
Its dual is the annihilator {v : J*v = 0}, exactly DEL-20's tangent.

This test independently computes the row rank over finite fields,
verifies annihilator/quotient dimension, checks explicit quotient
functional invariance under each defining relation, and detects
the nilpotent radical mutant.
"""
from __future__ import annotations

import itertools
import json
import unittest
from pathlib import Path

PRIMES=(2,3,5,7,11,13,17)
MODES=("parabola","node_origin","node_smooth","double_line",
       "radical_line","redundant","product_parabolas","char_two")


def rank_mod(matrix: list[list[int]], p: int) -> int:
    if not matrix:
        return 0
    A=[[a % p for a in row] for row in matrix]
    nrows,ncols=len(A),len(A[0])
    r=0
    for col in range(ncols):
        pivot=next((i for i in range(r,nrows) if A[i][col]),None)
        if pivot is None:
            continue
        A[r],A[pivot]=A[pivot],A[r]
        inv=pow(A[r][col],-1,p)
        A[r]=[v*inv%p for v in A[r]]
        for i in range(nrows):
            if i==r:
                continue
            c=A[i][col]
            A[i]=[(a-c*b)%p for a,b in zip(A[i],A[r])]
        r+=1
        if r==nrows:
            break
    return r


def frozen() -> list[dict]:
    rows=[]
    for n in range(160):
        p=2 if MODES[n%len(MODES)]=="char_two" else PRIMES[n%len(PRIMES)]
        mode=MODES[n%len(MODES)]
        x,y=(5*n+1)%p,(7*n+3)%p
        x1,y1=(11*n+2)%p,(13*n+5)%p
        if mode=="parabola":
            y=x*x%p
            J=[[-2*x,1]]
        elif mode=="node_origin":
            x=y=0
            J=[[0,0]]
        elif mode=="node_smooth":
            x,y=1,0
            J=[[0,1]]
        elif mode=="double_line":
            x=0
            J=[[0,0]]
        elif mode=="radical_line":
            x=0
            J=[[1,0]]
        elif mode=="redundant":
            x=0
            J=[[0,0],[0,0]]
        elif mode=="product_parabolas":
            y=x*x%p
            y1=x1*x1%p
            J=[[-2*x,1,0,0],[0,0,-2*x1,1]]
        elif mode=="char_two":
            x=(3*n+1)%p
            y=x*x%p
            J=[[0,1]]
        else:
            raise ValueError(mode)
        J=[[v%p for v in row] for row in J]
        ncoord=len(J[0])
        rr=rank_mod(J,p)
        rows.append({
            "id":f"DEL21D-{n+1:03d}",
            "field":f"F{p}",
            "mode":mode,
            "point":[x,y,x1,y1] if ncoord==4 else [x,y],
            "jacobian":J,
            "coordinates":ncoord,
            "rank":rr,
            "presented_cotangent_dim":ncoord-rr,
            "expected_tangent_count":p**(ncoord-rr),
        })
    return rows


def dot(p: int, x: tuple[int,...]|list[int],
        y: tuple[int,...]|list[int]) -> int:
    return sum(a*b for a,b in zip(x,y))%p


def is_tangent(J: list[list[int]], v: tuple[int,...], p: int) -> bool:
    return all(dot(p,row,v)==0 for row in J)


def row_span(J: list[list[int]], p: int) -> set[tuple[int,...]]:
    if not J:
        return {()}
    n=len(J[0])
    output=set()
    for lam in itertools.product(range(p),repeat=len(J)):
        output.add(tuple(sum(lam[j]*J[j][i] for j in range(len(J)))%p
                         for i in range(n)))
    return output


def gradients_for_mode(mode: str, point: list[int], p: int):
    x,y=point[:2]
    if mode=="parabola":
        return [[(-2*x)%p,1]]
    if mode=="node_origin" or mode=="node_smooth":
        return [[y%p,x%p]]
    if mode=="double_line":
        return [[(2*x)%p,0]]
    if mode=="radical_line":
        return [[1,0]]
    if mode=="redundant":
        return [[(2*x)%p,0],[(3*x*x)%p,0]]
    if mode=="product_parabolas":
        x1=point[2]
        return [[(-2*x)%p,1,0,0],[0,0,(-2*x1)%p,1]]
    if mode=="char_two":
        return [[(-2*x)%p,1]]
    raise ValueError(mode)


class PresentedCotangentFiberOracle(unittest.TestCase):
    def test_exact_manifest(self):
        path=Path(__file__).resolve().parents[1]/(
            "research/deligne_sign_audit/del21d_tasks.jsonl")
        loaded=[json.loads(s) for s in path.read_text().splitlines() if s]
        self.assertEqual(loaded,frozen())
        self.assertEqual(len(loaded),160)
        self.assertEqual(len({r["id"] for r in loaded}),160)
        self.assertEqual(
            {mode:sum(r["mode"]==mode for r in loaded) for mode in MODES},
            {mode:20 for mode in MODES})

    def test_actual_polynomial_gradient_rows(self):
        for r in frozen():
            p=int(r["field"][1:])
            self.assertEqual(r["jacobian"],
                             gradients_for_mode(r["mode"],r["point"],p),r)
            self.assertEqual(rank_mod(r["jacobian"],p),r["rank"],r)

    def test_tangent_annihilator_cardinality(self):
        for r in frozen():
            p=int(r["field"][1:])
            n=r["coordinates"]
            if n==4 and p>7:
                # Rank-nullity yields the same cardinality; avoid
                # unnecessary O(p^4) enumeration for large fields.
                self.assertEqual(r["rank"],2)
                self.assertEqual(r["expected_tangent_count"],p*p)
                continue
            count=sum(is_tangent(r["jacobian"],v,p)
                      for v in itertools.product(range(p),repeat=n))
            self.assertEqual(count,r["expected_tangent_count"],r)

    def test_presented_quotient_and_dual_have_matching_dimension(self):
        for r in frozen():
            p=int(r["field"][1:])
            n=r["coordinates"]
            rr=rank_mod(r["jacobian"],p)
            self.assertEqual(r["presented_cotangent_dim"],n-rr)
            self.assertEqual(r["expected_tangent_count"],p**(n-rr))

    def test_tangent_functionals_vanish_on_entire_row_span(self):
        for r in frozen():
            p=int(r["field"][1:])
            n=r["coordinates"]
            # Iterate all row-span elements with bounded small fields.
            if p>7:
                continue
            span=row_span(r["jacobian"],p)
            self.assertEqual(len(span),p**r["rank"])
            tangents=(v for v in itertools.product(range(p),repeat=n)
                      if is_tangent(r["jacobian"],v,p))
            for v in tangents:
                self.assertTrue(all(dot(p,v,row)==0 for row in span))

    def test_quotient_functional_well_defined(self):
        for r in frozen():
            p=int(r["field"][1:])
            if p>7:
                continue
            n=r["coordinates"]
            J=r["jacobian"]
            relations=row_span(J,p)
            v=next(v for v in itertools.product(range(p),repeat=n)
                   if is_tangent(J,v,p))
            for b in itertools.product(range(p),repeat=n):
                for rel in relations:
                    b2=tuple((b[i]+rel[i])%p for i in range(n))
                    self.assertEqual(dot(p,v,b),dot(p,v,b2))

    def test_nonreduced_radical_mutant(self):
        for p in PRIMES:
            # At x=0, gradient x^2 is zero. The radical x gives
            # a nonzero conormal relation, killing the x tangent.
            thick=[[0,0]]
            radical=[[1,0]]
            self.assertEqual(rank_mod(thick,p),0)
            self.assertEqual(rank_mod(radical,p),1)
            self.assertTrue(is_tangent(thick,(1,0),p))
            self.assertFalse(is_tangent(radical,(1,0),p))

    def test_redundant_generators_preserve_quotient(self):
        for p in PRIMES:
            # (x^2,x^3) has the same ideal and relation span as (x^2).
            self.assertEqual(rank_mod([[0,0]],p),
                             rank_mod([[0,0],[0,0]],p))
            self.assertEqual(row_span([[0,0]],p),
                             row_span([[0,0],[0,0]],p))

    def test_product_embedding_has_two_independent_rows(self):
        for r in frozen():
            if r["mode"]!="product_parabolas":
                continue
            p=int(r["field"][1:])
            self.assertEqual(rank_mod(r["jacobian"],p),2)
            self.assertEqual(r["presented_cotangent_dim"],2)
            x=r["point"][0]
            x1=r["point"][2]
            for a in range(p):
                for b in range(p):
                    v=(a,(2*x*a)%p,b,(2*x1*b)%p)
                    self.assertTrue(is_tangent(r["jacobian"],v,p))

    def test_characteristic_two_square_derivative(self):
        for r in frozen():
            if r["mode"]!="char_two":
                continue
            self.assertEqual(r["field"],"F2")
            self.assertEqual(r["jacobian"],[[0,1]])
            self.assertTrue(is_tangent(r["jacobian"],(1,0),2))


if __name__=="__main__":
    unittest.main()
